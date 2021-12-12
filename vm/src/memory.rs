use crate::Error;

#[derive(Clone)]
pub struct Memory {
    data: Vec<u8>,
}

impl Memory {
    pub fn new(size: usize) -> Self {
        Self {
            data: vec![0; size],
        }
    }

    pub fn size(&self) -> usize {
        self.data.len()
    }

    pub fn write(&mut self, addr: u64, byte: u8) -> Result<(), Error> {
        match self.data.get_mut(addr as usize) {
            Some(cell) => {
                *cell = byte;
                Ok(())
            }
            None => Err(Error::InvalidAddress),
        }
    }

    pub fn read(&self, addr: u64) -> Result<u8, Error> {
        match self.data.get(addr as usize) {
            Some(cell) => Ok(*cell),
            None => Err(Error::InvalidAddress),
        }
    }
}
