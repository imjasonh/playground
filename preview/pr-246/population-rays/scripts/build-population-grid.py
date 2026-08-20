#!/usr/bin/env python3
"""Build browser-ready US population grids from Meta/CIESIN HRSL COGs on AWS.

Requires: GDAL (osgeo), numpy.

Network: reads Cloud-Optimized GeoTIFFs via /vsicurl/ from
s3://dataforgood-fb-data/hrsl-cogs/ (no AWS credentials needed).

Usage:
  python3 scripts/build-population-grid.py
  python3 scripts/build-population-grid.py --out data
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import re
import sys
import tempfile
import time
import urllib.request


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        default=os.path.join(os.path.dirname(__file__), "..", "data"),
        help="Output directory for .f32.gz + JSON sidecars",
    )
    args = parser.parse_args()
    out = os.path.abspath(args.out)
    os.makedirs(out, exist_ok=True)

    try:
        from osgeo import gdal
        import numpy as np
    except ImportError as exc:
        print("Need GDAL Python bindings and numpy:", exc, file=sys.stderr)
        return 1

    gdal.UseExceptions()
    gdal.SetConfigOption("GDAL_DISABLE_READDIR_ON_OPEN", "EMPTY_DIR")
    gdal.SetConfigOption("CPL_VSIL_CURL_CACHE_SIZE", str(512 * 1024 * 1024))

    base = "https://dataforgood-fb-data.s3.us-east-1.amazonaws.com/hrsl-cogs/hrsl_general/"
    vrt_txt = urllib.request.urlopen(base + "hrsl_general-latest.vrt", timeout=60).read().decode()
    srcs = sorted(set(re.findall(r"SourceFilename[^>]*>([^<]+)", vrt_txt)))
    us = [
        s
        for s in srcs
        if re.search(
            r"lat_(20|30|40)_lon_(-1[0-3]0|-1[0-2]0|-110|-100|-90|-80|-70|-60)",
            s,
        )
    ]
    sources = [f"/vsicurl/{base}{s}" for s in us]
    print(f"Found {len(sources)} CONUS HRSL tiles")

    with tempfile.TemporaryDirectory(prefix="pop-rays-") as tmp:
        vrt_path = os.path.join(tmp, "us_hrsl.vrt")
        gdal.BuildVRT(vrt_path, sources)

        conus_tif = os.path.join(tmp, "conus.tif")
        print("Warping CONUS at 0.02° (sum)…")
        t0 = time.time()
        gdal.Warp(
            conus_tif,
            vrt_path,
            format="GTiff",
            xRes=0.02,
            yRes=0.02,
            outputBounds=(-125.0, 24.0, -66.0, 50.0),
            resampleAlg="sum",
            dstNodata=0,
            creationOptions=["COMPRESS=DEFLATE", "TILED=YES"],
        )
        print(f"  done in {time.time() - t0:.1f}s")
        pack(
            conus_tif,
            out,
            "conus-0p02",
            "Contiguous US ~2.2 km cells",
            np,
            gdal,
        )

        ne_tif = os.path.join(tmp, "ne.tif")
        ne_sources = [
            f"/vsicurl/{base}v1/cog_globallat_40_lon_-70_general-v1.1.tif",
            f"/vsicurl/{base}v1/cog_globallat_40_lon_-80_general-v1.1.tif",
        ]
        print("Warping Northeast at 0.005° (sum)…")
        t0 = time.time()
        gdal.Warp(
            ne_tif,
            ne_sources,
            format="GTiff",
            xRes=0.005,
            yRes=0.005,
            outputBounds=(-75.5, 40.0, -71.5, 42.0),
            resampleAlg="sum",
            dstNodata=0,
            creationOptions=["COMPRESS=DEFLATE", "TILED=YES"],
        )
        print(f"  done in {time.time() - t0:.1f}s")
        pack(
            ne_tif,
            out,
            "northeast-0p005",
            "NYC / Northeast ~550 m cells",
            np,
            gdal,
        )

    index = {
        "version": 1,
        "defaultDataset": "conus-0p02",
        "datasets": ["conus-0p02", "northeast-0p005"],
        "description": "Gridded residential population for directional corridor visualization.",
    }
    with open(os.path.join(out, "index.json"), "w", encoding="utf-8") as f:
        json.dump(index, f, indent=2)
        f.write("\n")
    print("Wrote", out)
    return 0


def pack(tif_path, out_dir, key, note, np, gdal):
    ds = gdal.Open(tif_path)
    gt = ds.GetGeoTransform()
    arr = np.nan_to_num(ds.ReadAsArray().astype(np.float32), nan=0.0, posinf=0.0, neginf=0.0)
    arr[arr < 0] = 0
    h, w = arr.shape
    west, cell, north = float(gt[0]), float(gt[1]), float(gt[3])
    south = north + h * float(gt[5])
    raw = arr.tobytes(order="C")
    gz = gzip.compress(raw, compresslevel=9)
    bin_name = f"{key}.f32.gz"
    with open(os.path.join(out_dir, bin_name), "wb") as f:
        f.write(gz)
    meta = {
        "key": key,
        "note": note,
        "west": west,
        "south": south,
        "north": north,
        "east": west + w * cell,
        "cellDeg": cell,
        "width": w,
        "height": h,
        "dtype": "float32",
        "endian": "little",
        "layout": "row-major",
        "nodata": 0,
        "units": "people-per-cell",
        "totalPopulation": float(arr.sum()),
        "nonzeroCells": int(np.count_nonzero(arr)),
        "maxCell": float(arr.max()),
        "bytesUncompressed": len(raw),
        "bytesGzip": len(gz),
        "sha256Uncompressed": hashlib.sha256(raw).hexdigest(),
        "source": {
            "name": "Meta / CIESIN High Resolution Settlement Layer (HRSL)",
            "url": "https://registry.opendata.aws/dataforgood-fb-hrsl/",
            "citation": (
                "Meta and Center for International Earth Science Information "
                "Network - CIESIN - Columbia University. 2022. High Resolution "
                "Settlement Layer (HRSL)."
            ),
            "license": "CC BY 4.0",
            "aggregation": "sum-resampled from ~30m population-count COGs",
        },
        "file": bin_name,
    }
    with open(os.path.join(out_dir, f"{key}.json"), "w", encoding="utf-8") as f:
        json.dump(meta, f, indent=2)
        f.write("\n")
    print(
        f"  {key}: gzip {len(gz)/1e6:.2f} MB, totalPop {meta['totalPopulation']:.0f}"
    )


if __name__ == "__main__":
    raise SystemExit(main())
