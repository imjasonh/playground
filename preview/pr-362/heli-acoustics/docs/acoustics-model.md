# Acoustics model (research basis)

This experiment auralizes a helicopter over a street canyon in the browser.
The solver is geometric acoustics plus Web Audio binaural rendering. The pieces
below are tied to published methods. Where the live code still approximates,
the gap is called out.

## Hybrid pipeline

| Stage | Method | Primary references |
|-------|--------|--------------------|
| Early specular | Image-source method (ISM), orders 1–3 | Allen & Berkley, JASA 66(4), 1979 |
| Late field | Stochastic ray tracing → energy histogram → noise IR | Vorländer; Wayverb / MATLAB acousticRoomResponse hybrid |
| Edge diffraction | Fresnel number + Maekawa insertion loss | Maekawa, Applied Acoustics 1, 1968; ISO 9613-2 screening |
| Soft occlusion | Continuous Maekawa attenuation into the shadow | Same as diffraction (barrier IL) |
| Atmosphere | ISO 9613-1 pure-tone absorption on each path | ISO 9613-1:1993 |
| Materials | Octave-ish absorption → pressure reflection β | Allen & Berkley β with α = 1 − β² |
| Scattering | Specular fraction (1 − s) on early paths; s into late | Kang, JASA 107(3), 2000 (street-canyon diffuse vs specular) |
| Spatialization | Browser HRTF `PannerNode` per path | Web Audio; HRTF interpolation practice as in ISM+HRTF demos |
| Spreading | Spherical pressure 1/R | Allen & Berkley (point-source Green’s function) |

Urban canyon motivation for specular *and* diffuse energy: Ismail & Oldham
(2002) on low-flying aircraft in street canyons; Thomas et al. / Ghent canyon
IR work combining ISM with a stochastic envelope for facade scatter.

## Formulas used in code

### Image source (Allen & Berkley)

Mirror the source across each planar facade (or the ground). Path length R is
the listener-to-image distance. Delay is R/c with c = 343 m/s. Pressure
amplitude scales as β_product / R (not 1/√R). Visibility requires the hit on
each face and clear segments between bounce points.

### Pressure reflection coefficient

For energy absorption coefficient α in a band,

β = √(1 − α)

(Allen & Berkley, Sabine relation α = 1 − β²). Specular path energy also keeps
fraction (1 − s) where s is the surface scattering coefficient; scattered
energy is left for the stochastic late field (Kang: diffuse boundaries change
canyon decay).

### Atmospheric absorption (ISO 9613-1)

Pure-tone attenuation coefficient α_air(f, T, RH, p) in dB/m. Path attenuation
in dB is α_air · R. Linear amplitude multiplies by 10^(−A_dB / 20). Default
meteorology is 20 °C, 50 % RH, 101.325 kPa. Band centers: 250 Hz, 1 kHz, 4 kHz.

### Diffraction and soft occlusion (Maekawa)

Path difference δ = R_diffracted − R_direct. Fresnel number at frequency f:

N = 2 δ / λ,  λ = c / f

Maekawa insertion loss (dB), capped at 25 dB:

IL = 10 log₁₀(3 + 20 N)   for N > 0, else 0 in the illuminated zone

Diffracted taps use IL at low/mid/high band centers with geometric 1/(d₁ d₂)
edge-source style falloff (BTM / Svensson secondary-source intuition, not a
full BTM line integral). When the direct ray hits a building, dry-path
occlusion is the continuous factor 1 − 10^(−IL_best / 20) from the best edge,
not a hard mute.

### Stochastic late field

Rays leave the source, bounce with absorption and a specular/random mix
controlled by s, and deposit energy into delay bins (diffused-rain style). The
histogram weights decorrelated noise for a `ConvolverNode` IR (standard
auralization practice when full audio-rate tracing is too expensive).

### Doppler

Radial source velocity toward the listener shifts the dry oscillator:

f′ = f · c / (c − v_radial)

with |v_radial| clamped below ~0.9 c.

## Known gaps vs research-grade outdoor tools

Full Biot–Tolstoy–Medwin edge integrals (Svensson et al.), complex ground
impedance (Delany–Bazley), wind/temperature refraction, source directivity of
a real rotorcraft, measured facade scattering, and SOFA HRTFs are not in this
build. Wave solvers (FDTD / PSTD) would be needed for low-frequency canyon
modes that geometric acoustics miss.

The goal here is a **physically motivated real-time auralization** you can A/B
in headphones, not a regulatory noise map.
