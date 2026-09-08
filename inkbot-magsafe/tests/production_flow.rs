use inkbot_magsafe::panel::{
    apply_patch, RefreshKind, RefreshPolicy, Window, FRAME_BYTES, ROW_BYTES,
};
use inkbot_magsafe::power::{refresh_decision, ChargerStatus, PowerSample, EVT_SAFETY_LIMITS};
use inkbot_magsafe::protocol::{Accept, Begin, Crc32, FrameHeader, FrameSink, Receiver};
use inkbot_magsafe::storage::{
    scan_metadata_journal, select_latest_verified, FrameRecord, FrameSlot,
    METADATA_JOURNAL_BYTES, METADATA_RECORD_BYTES,
};

struct PayloadSink {
    bytes: Vec<u8>,
}

impl FrameSink for PayloadSink {
    type Error = ();

    fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
        let start = offset as usize;
        let end = start + bytes.len();
        self.bytes[start..end].copy_from_slice(bytes);
        Ok(())
    }
}

fn crc32(bytes: &[u8]) -> u32 {
    let mut crc = Crc32::new();
    crc.update(bytes);
    crc.finalize()
}

#[test]
fn partial_transfer_survives_each_power_fail_boundary() {
    let old_image = vec![0xff; FRAME_BYTES];
    let old_frame = FrameHeader {
        id: 40,
        len: FRAME_BYTES as u32,
        crc: crc32(&old_image),
        window: Window::FULL,
    };
    let mut old_receiver = Receiver::new();
    assert_eq!(old_receiver.begin(old_frame), Ok(Begin::Started));
    let mut old_sink = PayloadSink {
        bytes: vec![0; FRAME_BYTES],
    };
    assert_eq!(
        old_receiver.ingest(0, &old_image, &mut old_sink),
        Ok(Accept::Complete)
    );
    let old_committed = old_receiver.commit().unwrap();
    let old_record = FrameRecord {
        generation: 10,
        slot: FrameSlot::A,
        image_crc: old_frame.crc,
        frame: old_committed,
    };
    assert!(old_record.verifies_image(&old_image));
    let mut journal = [0xff; METADATA_JOURNAL_BYTES];
    journal[..METADATA_RECORD_BYTES].copy_from_slice(&old_record.to_bytes());

    let patch = [0x00, 0x11, 0x22, 0x33];
    let window = Window {
        x: 16,
        y: 3,
        w: 16,
        h: 2,
    };
    let header = FrameHeader {
        id: 41,
        len: patch.len() as u32,
        crc: crc32(&patch),
        window,
    };
    let mut receiver = Receiver::with_last_completed(old_committed);
    assert_eq!(receiver.begin(header), Ok(Begin::Started));
    let mut sink = PayloadSink {
        bytes: vec![0; patch.len()],
    };
    assert_eq!(
        receiver.ingest(0, &patch[..2], &mut sink),
        Ok(Accept::Progress(2))
    );
    assert_eq!(
        receiver.ingest(2, &patch[2..], &mut sink),
        Ok(Accept::Complete)
    );

    // A reset before metadata commit still selects the old, verified image.
    assert_eq!(
        scan_metadata_journal(&journal).unwrap().latest,
        Some(old_record)
    );

    let mut candidate_image = old_image.clone();
    apply_patch(&mut candidate_image, window, &sink.bytes).unwrap();
    assert_eq!(
        &candidate_image[3 * ROW_BYTES + 2..3 * ROW_BYTES + 4],
        &[0x00, 0x11]
    );
    let new_record = FrameRecord {
        generation: 11,
        slot: old_record.slot.next(),
        image_crc: crc32(&candidate_image),
        frame: receiver.verified_frame().unwrap(),
    };
    assert!(new_record.verifies_image(&candidate_image));
    let mut corrupted_image = candidate_image.clone();
    corrupted_image[FRAME_BYTES / 2] ^= 1;
    assert!(!new_record.verifies_image(&corrupted_image));

    // A torn metadata write is ignored, so the old slot remains authoritative.
    let encoded = new_record.to_bytes();
    journal[METADATA_RECORD_BYTES..METADATA_RECORD_BYTES + 20]
        .copy_from_slice(&encoded[..20]);
    let interrupted = scan_metadata_journal(&journal).unwrap();
    assert_eq!(interrupted.latest, Some(old_record));
    assert_eq!(interrupted.invalid_records, 1);

    let next = interrupted.next_write;
    assert_eq!(next.erase_page, None);
    journal[next.offset..next.offset + METADATA_RECORD_BYTES].copy_from_slice(&encoded);
    let durable = scan_metadata_journal(&journal).unwrap().latest.unwrap();
    assert_eq!(durable, new_record);
    assert_eq!(
        select_latest_verified(&[
            (old_record, &old_image),
            (durable, &candidate_image),
        ]),
        Some(new_record)
    );
    assert_eq!(receiver.commit(), Some(durable.frame));

    // A reboot restores the replay boundary and can repaint from the full slot.
    let mut rebooted = Receiver::with_last_completed(durable.frame);
    assert_eq!(rebooted.begin(header), Ok(Begin::AlreadyCommitted));
    assert_eq!(
        refresh_decision(
            PowerSample {
                sys_mv: 3800,
                qi_present: false,
                charger: ChargerStatus::InputAbsent,
                panel_temp_c: Some(22),
            },
            EVT_SAFETY_LIMITS,
        ),
        Ok(())
    );
    let policy = RefreshPolicy::new();
    let plan = policy.choose(RefreshKind::Partial, window);
    assert_eq!(plan.kind(), RefreshKind::Full);
    assert_eq!(plan.window(), Window::FULL);
}
