use std::sync::atomic::{AtomicU8, Ordering::Relaxed};
use std::sync::Arc;

pub struct Timer {}

impl Timer {
    pub fn new(irq: Arc<AtomicU8>) -> Self {
        std::thread::spawn(move || thread_timer(irq));
        Self {}
    }
}

fn thread_timer(irq: Arc<AtomicU8>) {
    let target_delta = std::time::Duration::from_millis(1);
    loop {
        let start = std::time::Instant::now();
        irq.store(spec::Irq::Timer as u8, Relaxed);
        while start.elapsed() < target_delta {
            std::hint::spin_loop();
        }
    }
}
