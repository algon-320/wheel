use num_traits::{WrappingAdd, WrappingMul, WrappingSub};

pub trait LittleEndian {
    type Bytes: Default + AsRef<[u8]> + AsMut<[u8]>;
    fn from_le_bytes(bytes: Self::Bytes) -> Self;
    fn to_le_bytes(self) -> Self::Bytes;
}

macro_rules! impl_little_endian {
    ($t:ty) => {
        impl LittleEndian for $t {
            type Bytes = [u8; std::mem::size_of::<$t>()];
            fn from_le_bytes(bytes: Self::Bytes) -> Self {
                <$t>::from_le_bytes(bytes)
            }
            fn to_le_bytes(self) -> Self::Bytes {
                self.to_le_bytes()
            }
        }
    };
}

impl_little_endian! {u8}
impl_little_endian! {u16}
impl_little_endian! {u32}
impl_little_endian! {u64}

pub trait Int:
    LittleEndian
    + Eq
    + Copy
    + Ord
    + std::ops::Add<Output = Self>
    + std::ops::Sub<Output = Self>
    + std::ops::Mul<Output = Self>
    + std::ops::Div<Output = Self>
    + std::ops::BitAnd<Output = Self>
    + std::ops::BitOr<Output = Self>
    + std::ops::BitXor<Output = Self>
    + std::ops::Not<Output = Self>
    + WrappingAdd
    + WrappingMul
    + WrappingSub
    + std::fmt::Display
    + std::fmt::Debug
{
}
impl<T> Int for T where
    T: LittleEndian
        + Eq
        + Copy
        + Ord
        + std::ops::Add<Output = Self>
        + std::ops::Sub<Output = Self>
        + std::ops::Mul<Output = Self>
        + std::ops::Div<Output = Self>
        + std::ops::BitAnd<Output = Self>
        + std::ops::BitOr<Output = Self>
        + std::ops::BitXor<Output = Self>
        + std::ops::Not<Output = Self>
        + WrappingAdd
        + WrappingMul
        + WrappingSub
        + std::fmt::Display
        + std::fmt::Debug
{
}
