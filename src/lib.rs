
#![feature(test)]

extern crate test;
extern crate unicode_width;
extern crate memchr;

#[cfg(test)]
const TEST_TEXT: &str = include_str!("base.rs.txt");




/// Identifies an offset of a multi-byte character in a FileMap
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct MultiByteChar {
    /// The absolute offset of the character in the CodeMap
    pub pos: u32,
    /// The number of bytes, >=2
    pub bytes: usize,
}

/// Identifies an offset of a non-narrow character in a FileMap
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum NonNarrowChar {
    /// Represents a zero-width character
    ZeroWidth(u32),
    /// Represents a wide (fullwidth) character
    Wide(u32),
    /// Represents a tab character, represented visually with a width of 4 characters
    Tab(u32),
}

impl NonNarrowChar {
    fn new(pos: u32, width: usize) -> Self {
        match width {
            0 => NonNarrowChar::ZeroWidth(pos),
            2 => NonNarrowChar::Wide(pos),
            4 => NonNarrowChar::Tab(pos),
            _ => panic!("width {} given for non-narrow character", width),
        }
    }

    /// Returns the absolute offset of the character in the CodeMap
    pub fn pos(&self) -> u32 {
        match *self {
            NonNarrowChar::ZeroWidth(p) |
            NonNarrowChar::Wide(p) |
            NonNarrowChar::Tab(p) => p,
        }
    }

    /// Returns the width of the character, 0 (zero-width) or 2 (wide)
    pub fn width(&self) -> usize {
        match *self {
            NonNarrowChar::ZeroWidth(_) => 0,
            NonNarrowChar::Wide(_) => 2,
            NonNarrowChar::Tab(_) => 4,
        }
    }
}





pub struct Result {
    pub lines: Vec<u32>,
    pub mbcs: Vec<MultiByteChar>,
    pub nncs: Vec<NonNarrowChar>,
}

impl Result {
    #[inline]
    fn add_mbcs(&mut self, pos: u32, bytes: usize) {
        self.mbcs.push(MultiByteChar {
            pos,
            bytes,
        });
    }

    #[inline]
    pub fn record_width(&mut self, pos: u32, ch: char) {
        let width = match ch {
            '\t' =>
                // Tabs will consume 4 columns.
                4,
            '\n' =>
                // Make newlines take one column so that displayed spans can point them.
                1,
            ch =>
                // Assume control characters are zero width.
                // FIXME: How can we decide between `width` and `width_cjk`?
                unicode_width::UnicodeWidthChar::width(ch).unwrap_or(0),
        };
        // Only record non-narrow characters.
        if width != 1 {
            self.nncs.push(NonNarrowChar::new(pos, width));
        }
    }
}

fn char_at(s: &str, pos: u32) -> char {
    s[pos as usize ..].chars().next().unwrap()
}

#[inline]
fn is_aligned(src: &str) -> bool {
    (src.as_ptr() as usize) % 16 == 0
}

fn align(mut src: &str) -> &str {
    while !is_aligned(src) {
        src = &src[1..];
    }
    src
}

fn align_string(s: &mut String) -> &str {
    let mut start = 0;

    while !is_aligned(&s[start..]) {
        s.insert(0, ' ');
        start += 1;
    }

    &s[start..]
}

macro_rules! fn_with_test {
    (fn $name:ident ( $text:ident : &str, $start:ident : u32 ) -> Result $body:expr) => (
        pub mod $name {
            use super::*;

            pub fn analyze($text: &str, $start: u32) -> Result {
                return $body;
            }

            #[test]
            fn test_lines() {
                let mut text = "aaaaa\nbbbbBB\nCCC\nDDDDDddddd".to_string();
                let text = align_string(&mut text);
                let result = analyze(text, 0);
                assert_eq!(result.lines, vec![0, 6, 13, 17]);

                let result = analyze(text, 10);
                assert_eq!(result.lines, vec![10, 16, 23, 27]);
            }

            #[test]
            fn test_mbcs() {
                let mut text = "aüxüa".to_string();
                let text = align_string(&mut text);
                let result = analyze(text, 0);
                assert_eq!(result.mbcs, vec![
                    MultiByteChar { pos: 1, bytes: 2 },
                    MultiByteChar { pos: 4, bytes: 2 },
                ]);

                let result = analyze(text, 10);
                assert_eq!(result.mbcs, vec![
                    MultiByteChar { pos: 11, bytes: 2 },
                    MultiByteChar { pos: 14, bytes: 2 },
                ]);
            }

            #[test]
            fn test_nncs() {
                let mut text = "a\tx\ra".to_string();
                let text = align_string(&mut text);
                let result = analyze(text, 0);
                assert_eq!(result.nncs, vec![
                    NonNarrowChar::new(1, 4),
                    NonNarrowChar::new(3, 0),
                ]);

                let result = analyze(text, 10);
                assert_eq!(result.nncs, vec![
                    NonNarrowChar::new(11, 4),
                    NonNarrowChar::new(13, 0),
                ]);
            }

            #[bench]
            fn bench(b: &mut ::test::Bencher) {
                b.iter(|| {
                    let text = ::test::black_box(align(super::TEST_TEXT));
                    ::test::black_box(analyze(text, 0));
                })
            }
        }
    );
}

fn_with_test!(fn naive(src: &str, offset: u32) -> Result {

    let mut result = Result {
        lines: vec![],
        mbcs: vec![],
        nncs: vec![],
    };

    let mut prev_char = '\n';

    let mut i = 0u32;
    let src_len = src.len() as u32;

    while i < src_len {
        if prev_char == '\n' {
            result.lines.push(i + offset);
        }

        let c = char_at(src, i);
        let len = c.len_utf8();
        if len > 1 {
            result.add_mbcs(i + offset, len);
        }

        result.record_width(i + offset, c);

        prev_char = c;
        i += len as u32;
    }

    result
});


fn_with_test!(fn simple_ascii(src: &str, offset: u32) -> Result {
    let mut result = Result {
        lines: vec![offset],
        mbcs: vec![],
        nncs: vec![],
    };

    let mut i = 0u32;
    let src_len = src.len() as u32;

    while i < src_len {
        let byte = unsafe {
            *src.as_bytes().get_unchecked(i as usize)
        };

        let pos = i + offset;

        if byte.is_ascii() {
            match byte {
                b'\n' => {
                    result.lines.push(pos + 1);
                }
                b'\t' => {
                    result.nncs.push(NonNarrowChar::Tab(pos));
                }
                c => if c.is_ascii_control() {
                    result.nncs.push(NonNarrowChar::ZeroWidth(pos));
                }
            }

            i += 1;
        } else {
            let c = char_at(src, i);
            let len = c.len_utf8();
            result.add_mbcs(pos, len);
            result.record_width(pos, c);
            i += len as u32;
        }
    }

    if result.lines.last().cloned() == Some(src_len + offset) {
        result.lines.pop();
    }

    result
});





const ASCII_MASK: u64 = 0b1000_0000u64 << 0 |
                        0b1000_0000u64 << 8 |
                        0b1000_0000u64 << 16 |
                        0b1000_0000u64 << 24 |
                        0b1000_0000u64 << 32 |
                        0b1000_0000u64 << 40 |
                        0b1000_0000u64 << 48 |
                        0b1000_0000u64 << 56;

fn_with_test!(fn chunk_ascii(src: &str, offset: u32) -> Result {
    let mut result = Result {
        lines: vec![offset],
        mbcs: vec![],
        nncs: vec![],
    };

    assert!(is_aligned(src));

    let chunks = (src.len() / 8) as u32;

    let mut chunk_internal_offset = 0;

    for chunk_index in 0 .. chunks {
        let chunk = unsafe {
            *(src.as_ptr() as *const u64).offset(chunk_index as isize)
        };

        let all_ascii = (chunk & ASCII_MASK) == 0;

        if chunk_internal_offset == 0 && all_ascii {

            let chunk_start = (chunk_index * 8 + offset) as u32;
            for i in 0 .. 8 {
                let pos = i + chunk_start;
                let byte = (chunk >> (i * 8)) as u8;

                match byte {
                    b'\n' => {
                        result.lines.push(pos + 1);
                    }
                    b'\t' => {
                        result.nncs.push(NonNarrowChar::Tab(pos));
                    }
                    c => if c.is_ascii_control() {
                        result.nncs.push(NonNarrowChar::ZeroWidth(pos));
                    }
                }
            }
        } else {
            let chunk_start = chunk_index * 8;
            let chunk_end = chunk_start + 8;

            let mut i = chunk_start + chunk_internal_offset;

            while i < chunk_end {
                let c = char_at(src, i);
                let len = c.len_utf8();

                if c == '\n' {
                    result.lines.push(i + offset + 1);
                }

                if len > 1 {
                    result.add_mbcs(i + offset, len);
                }
                result.record_width(i + offset, c);
                i += len as u32;
            }
            chunk_internal_offset = i - chunk_end;
            debug_assert!(chunk_internal_offset < 8);
        }
    }

    let rest_start = chunks * 8;
    let rest_end = src.len() as u32;

    let mut i = rest_start;

    while i < rest_end {
        let c = char_at(src, i);
        let len = c.len_utf8();

        if c == '\n' {
            result.lines.push(i + offset + 1);
        }

        if len > 1 {
            result.add_mbcs(i + offset, len);
        }
        result.record_width(i + offset, c);
        i += len as u32;
    }

    result
});


fn_with_test!(fn ascii_opt1(src: &str, offset: u32) -> Result {
    let mut result = Result {
        lines: vec![offset],
        mbcs: vec![],
        nncs: vec![],
    };

    let mut i = 0u32;
    let src_len = src.len() as u32;
    let src_bytes = src.as_bytes();

    while i < src_len {
        let byte = unsafe {
             *src_bytes.get_unchecked(i as usize)
        };

        let mut step = 1;

        if byte < 32 {
            let pos = i + offset;

            match byte {
                b'\n' => {
                    result.lines.push(pos + 1);
                }
                b'\t' => {
                    result.nncs.push(NonNarrowChar::Tab(pos));
                }
                _ => {
                    result.nncs.push(NonNarrowChar::ZeroWidth(pos));
                }
            }
        } else if byte >= 127 {
            let pos = i + offset;
            let c = char_at(src, i);
            let len = c.len_utf8();
            result.add_mbcs(pos, len);
            result.record_width(pos, c);
            step = len as u32;
        }

        i += step;
    }

    if result.lines.last().cloned() == Some(src_len + offset) {
        result.lines.pop();
    }

    result
});

fn_with_test!(fn no_non_narrow(src: &str, offset: u32) -> Result {
    let mut result = Result {
        lines: vec![offset],
        mbcs: vec![],
        nncs: vec![],
    };

    let mut i = 0u32;
    let src_len = src.len() as u32;

    while i < src_len {
        let byte = unsafe {
            *src.as_bytes().get_unchecked(i as usize)
        };

        let mut step = 1;

        if byte == b'\n' {
            result.lines.push(i + offset + 1);
        }

        if byte > 127 {
            let pos = i + offset;
            let c = char_at(src, i);
            let len = c.len_utf8();
            result.add_mbcs(pos, len);
            result.record_width(pos, c);
            step = len as u32;
        }

        i += step;
    }

    if result.lines.last().cloned() == Some(src_len + offset) {
        result.lines.pop();
    }

    result
});

const ASCII_MASK_128: u128 = (ASCII_MASK as u128) | ((ASCII_MASK as u128) << 64);

fn_with_test!(fn memchar(src: &str, offset: u32) -> Result {
    let mut result = Result {
        lines: vec![offset],
        mbcs: vec![],
        nncs: vec![],
    };

    let mut src_bytes = src.as_bytes();
    let src_len = src.len() as u32;

    loop {
        if let Some(index) = memchr::memchr(b'\n', src_bytes) {
            result.lines.push(index as u32 + offset + 1);
            src_bytes = &src_bytes[index + 1 ..];
        } else {
            break
        }
    }

    assert!(is_aligned(src));

    let chunks = src_len / 16;

    let mut need = false;

    unsafe {
        let start = src.as_ptr() as *const u128;
        let end = start.offset(chunks as isize);

        let mut p = start;

        while p != end {
            let chunk: u128 = *p;
            let all_ascii = (chunk & ASCII_MASK_128) == 0;

            if !all_ascii {
                need = true;
                break
            }

            p = p.offset(1);
        }
    }

    if need {
        let mut i = 0u32;

        while i < src_len {
            let byte = unsafe {
                *src_bytes.get_unchecked(i as usize)
            };

            let mut step = 1;

            if byte > 127 {
                let pos = i + offset;
                let c = char_at(src, i);
                let len = c.len_utf8();
                result.add_mbcs(pos, len);
                result.record_width(pos, c);
                step = len as u32;
            }

            i += step;
        }
    }

    result
});


fn_with_test!(fn simd_128(src: &str, offset: u32) -> Result {

    const CHUNK_SIZE: u32 = 16;

    use std::arch::x86_64::*;

    let mut result = Result {
        lines: vec![offset],
        mbcs: vec![],
        nncs: vec![],
    };

    let mut src_bytes = src.as_bytes();
    let src_len = src.len() as u32;

    let chunks = src_len / CHUNK_SIZE;

    let (control, big, newlines) = unsafe {
        (_mm_set1_epi8(32), _mm_set1_epi8(126), _mm_set1_epi8(10))
    };

    for i in 0 .. chunks {
        unsafe {
            let ptr = src_bytes.as_ptr() as *const __m128i;
            let chunk: __m128i = _mm_loadu_si128(ptr.offset(i as isize));

            let any_big = _mm_cmpgt_epi8(chunk, big);
            let any_big = _mm_movemask_epi8(any_big);

            if any_big == 0 {
                let any_control = _mm_cmplt_epi8(chunk, control);
                let any_control = _mm_movemask_epi8(any_control);

                if any_control != 0 {
                    let newlines = _mm_cmpeq_epi8(chunk, newlines);
                    let newlines = _mm_movemask_epi8(newlines);

                    if any_control == newlines {
                        let mut mask = 0xFFFF0000 | newlines as u32;

                        let offset = i * 8 + offset + 1;

                        loop {
                            let index = mask.trailing_zeros();

                            if index >= CHUNK_SIZE {
                                break
                            }

                            result.lines.push(index + offset);

                            mask &= (!1) << index;
                        }
                    }
                } else {
                    // no control characters, nothing to do
                }

                continue
            }
        }

        let mut i = i * CHUNK_SIZE;
        let end = i + CHUNK_SIZE;

        while i < end {
            let byte = unsafe {
                *src.as_bytes().get_unchecked(i as usize)
            };

            let mut step = 1;

            if byte < 32 || byte > 127 {

                if byte == b'\n' {
                    result.lines.push(i + offset + 1);
                }


                let pos = i + offset;
                let c = char_at(src, i);
                let len = c.len_utf8();

                if len > 1 {
                    result.add_mbcs(pos, len);
                }
                result.record_width(pos, c);
                step = len as u32;
            }

            i += step;
        }
    }

    let mut i = chunks * CHUNK_SIZE;

    while i < src_len {
        let byte = unsafe {
            *src_bytes.get_unchecked(i as usize)
        };

        let mut step = 1;

        let pos = i + offset;
        let c = char_at(src, i);
        let len = c.len_utf8();
        if len > 1 {
            result.add_mbcs(pos, len);
        }
        result.record_width(pos, c);
        step = len as u32;

        if c == '\n' {
            result.lines.push(pos + 1);
        }

        i += step;
    }

    result
});
