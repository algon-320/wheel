use crate::Error;
use spec::MmioBase;
const ADDR_DATA: u64 = MmioBase::BasicSerial as u64;
const ADDR_STATUS: u64 = MmioBase::BasicSerial as u64 + 1;

use std::sync::{Arc, Condvar, Mutex};

const STATUS_CAN_SEND: u8 = 1;
const STATUS_CAN_RECV: u8 = 2;

#[derive(Clone)]
struct Registers {
    status: u8,
    send_buf: u8,
    recv_buf: u8,
}
impl Registers {
    fn new() -> Self {
        Self {
            status: STATUS_CAN_SEND,
            recv_buf: 0,
            send_buf: 0,
        }
    }
}

#[derive(Clone)]
pub struct BasicSerial {
    regs: Arc<Mutex<Registers>>,
    send_ready: Arc<Condvar>,
    recv_ready: Arc<Condvar>,
}

impl BasicSerial {
    pub fn new() -> Self {
        let regs = Arc::new(Mutex::new(Registers::new()));
        let send_ready = Arc::new(Condvar::new());
        let recv_ready = Arc::new(Condvar::new());

        std::thread::spawn({
            let regs = regs.clone();
            let send_ready = send_ready.clone();
            move || thread_stdout(regs, send_ready)
        });

        std::thread::spawn({
            let regs = regs.clone();
            let recv_ready = recv_ready.clone();
            move || thread_stdin(regs, recv_ready)
        });

        Self {
            regs,
            send_ready,
            recv_ready,
        }
    }

    #[inline]
    pub fn write(&mut self, addr: u64, byte: u8) -> Result<(), Error> {
        match addr {
            ADDR_DATA => {
                let mut regs = self.regs.lock().unwrap();
                regs.send_buf = byte;
                regs.status &= !STATUS_CAN_SEND;
                self.send_ready.notify_one();
                Ok(())
            }

            ADDR_STATUS => {
                eprintln!("status is a readonly register");
                Err(Error::InvalidAddress)
            }

            _ => Err(Error::InvalidAddress),
        }
    }

    #[inline]
    pub fn read(&self, addr: u64) -> Result<u8, Error> {
        match addr {
            ADDR_DATA => {
                let mut regs = self.regs.lock().unwrap();
                let data = regs.recv_buf;
                regs.status &= !STATUS_CAN_RECV;
                self.recv_ready.notify_one();
                Ok(data)
            }
            ADDR_STATUS => {
                let regs = self.regs.lock().unwrap();
                Ok(regs.status)
            }
            _ => Err(Error::InvalidAddress),
        }
    }
}

fn thread_stdout(regs: Arc<Mutex<Registers>>, send_ready: Arc<Condvar>) {
    use std::io::Write;
    loop {
        let data = {
            let mut regs = regs.lock().unwrap();
            while (regs.status & STATUS_CAN_SEND) != 0 {
                regs = send_ready.wait(regs).unwrap();
            }
            regs.status |= STATUS_CAN_SEND;
            regs.send_buf
        };

        let mut stdout = std::io::stdout();
        stdout.write_all(&[data]).unwrap();
        stdout.flush().unwrap();
    }
}

fn thread_stdin(regs: Arc<Mutex<Registers>>, recv_ready: Arc<Condvar>) {
    use std::io::Read;
    loop {
        let mut buf = [0; 1];
        std::io::stdin().read_exact(&mut buf).expect("read stdin");
        let data = buf[0];

        let mut regs = regs.lock().unwrap();
        while (regs.status & STATUS_CAN_RECV) != 0 {
            regs = recv_ready.wait(regs).unwrap();
        }

        regs.recv_buf = data;
        regs.status |= STATUS_CAN_RECV;
    }
}
