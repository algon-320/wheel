use std::alloc::{alloc, Layout};
use std::ptr::copy_nonoverlapping;

#[link(name = "vm", kind = "static")]
extern "C" {
    fn vm_main(text: *mut u8, stack: *mut u8) -> u64; // FIXME: the return is not always u64
}

fn main() {
    let mut memsize = 0x1000;

    let mut args = std::env::args();
    args.next(); // ignore executable name

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-m" | "--mem" => {
                memsize = args.next().unwrap().parse::<usize>().unwrap();
            }
            unknown => {
                panic!("unknown option: {:?}", unknown);
            }
        }
    }

    let layout = Layout::from_size_align(memsize, 0x1000).expect("invalid layout");
    assert!(layout.size() > 0);
    let mem = unsafe { alloc(layout) };
    assert!(!mem.is_null());

    let text = std::fs::read("./out.bin").expect("read");
    assert!(text.len() < layout.size());
    unsafe { copy_nonoverlapping(text.as_ptr(), mem, text.len()) };

    let result = unsafe {
        let text = mem;
        let stack = mem.add(layout.size());
        vm_main(text, stack)
    };
    println!("{}", result);
}
