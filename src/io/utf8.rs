//! Tools for UTF-8 conversion.
//!
//! # UTF-8 Stream Decoding
//! 
//! The main functionality of [`reword`] is to process text files that are
//!     encoded as UTF-8.
//! The core of [`reword`]'s internal operates on a stream of [`char`]s,
//!     which is some implementation of [`Iterator`]`<Item = char>`.
//! The conversion from a UTF-8-encoded text file to a stream of [`char`]s 
//!     can be done with Rust's standard library rather easily as follows:
//! 
//! ```no_run
//! let string = std::fs::read_to_string("foo.txt").unwrap();
//! let stream = string.chars();
//! for c in stream {
//!     // Do something with c.
//! }
//! ```
//! 
//! However, in the case where
//!     random access (availble in the variable `string` above) is not needed,
//!     better memory efficiency can be achieved.
//! [`read_utf8_stream`] provides this restricted functionality with
//!     better memory efficiency and ease of use:
//! 
//! ```no_run
//! use reword::io::read_utf8_stream;
//! let stream = read_utf8_stream("foo.txt", 4096).unwrap();
//! for c in stream {
//!     // Do something with c.
//! }
//! ```
//! 
//! The number `4096` can be adjusted to control the memory usage.
//! See the documentation of [`read_utf8_stream`] for more information.
//! 
//! ## Further details
//! 
//! Also included in this module is the struct [`Utf8BufReaderStream`],
//!     which is a part of the return type of [`read_utf8_stream`].
//! [`Utf8BufReaderStream`] acts as an [`Iterator`]`<Item = char>` with
//!     an additional functionality for probing IO errors that
//!     may occur.
//! See the documentation of [`Utf8BufReaderStream`] for more detail.
//! 
//! [`reword`]: crate
//! [`read_to_string`]: std::fs::read_to_string

use std::fs::File;
use std::io::{BufRead, BufReader, Error, Result};
use std::path::Path;
use std::str::Chars;

/// The minimum size of buffer that will allow [`Utf8BufReaderStream`]
///     to work properly.
/// This number is equal to the maximum size (in bytes) of
///     one unicode character in UTF-8 encoding.
pub const MIN_BUFFER_SIZE: usize = 4;

/// Reads a stream of `[char]`s from a UTF-8 encoded file.
/// 
/// `path` is the path to the file, and
///     `max_buffer_size` is the bound on the size of the buffer that is used
///     for reading.
/// 
/// `read_utf8_stream` attempts to read the given file in chunks
///     (via [`BufReader`]).
/// The size of each chunk is controlled by `max_buffer_size` and
///     and the actual file size.
/// For the purpose of this discussion,
///     let `file_size` be the size of the file pointed to by `path`.
/// - If `max_buffer_size` is larger than `file_size`,
///     the buffer size will be `file_size + 1`.
/// - Otherwise, `max_buffer_size` will be the buffer size.
/// In the rare case where the file size cannot be retrieved
///     from the file system,
///     consider `file_size` to be [`usize::MAX`].
///
/// # Example
/// 
/// ```no_run
/// use reword::io::read_utf8_stream;
/// let stream = read_utf8_stream("foo.txt", 1048).unwrap();
/// println!("The file contains {} unicode letters.", stream.count());
/// ```
/// 
/// [`BufReader`]: std::io::BufReader
pub fn read_utf8_stream<P>(path: P, max_buffer_size: usize)
-> Result<Utf8BufReaderStream<BufReader<File>>>
where P: AsRef<Path> {
    use std::convert::TryInto;
    let file = File::open(path)?;
    let file_size_p1 = file.metadata().
        map_or(
            usize::MAX,
            |m| m.len().try_into().map_or(
                usize::MAX,
                |file_size: usize| {
                    if file_size == usize::MAX {
                        usize::MAX
                    } else {
                        file_size + 1
                    }
                }
            )
        );
    let buf_reader =
        BufReader::with_capacity(
            std::cmp::max(MIN_BUFFER_SIZE,
                std::cmp::min(max_buffer_size,
                    file_size_p1
            )),
            file
        );
    Ok(Utf8BufReaderStream::new(buf_reader))
}

/// Error type reported by [`Utf8BufReaderStream`].
/// See [`err`] for more information.
/// 
/// This is a sum type of [`Error`] and [`usize`],
///     where the second variant (`usize`) indicates
///     where the UTF-8 decoding error occurs.
/// 
/// [`err`]: Utf8BufReaderStream::err
/// [`Error`]: std::io::Error
#[derive(Debug)]
pub enum Utf8BufReaderError {
    /// Error that comes from reading the input.
    Reading(Error),
    /// Error that comes from decoding the input.
    /// 
    /// The [`usize`] value says how many bytes had been
    ///     successfully decoded before the failure occurred.
    /// Equivalently, this number is the offset into the input stream
    ///     where decoding fails.
    Decoding(usize),
}

impl Utf8BufReaderError {
    /// Returns [`None`] if this is not a decoding error.
    /// Otherwise, returns [`Some`]`(len)`,
    ///     where `len` is the offset into the input stream
    ///     where decoding fails.
    pub fn decoding_err(&self) -> Option<usize> {
        match self {
            Utf8BufReaderError::Decoding(len) => Some(*len),
            _ => None,
        }
    }

    /// Returns [`None`] if this is not a reading error.
    /// Otherwise, returns [`Some`]`(err)`,
    ///     where `err` is a reference to the reading error
    ///     returned from a call to [`fill_buf`].
    /// 
    /// [`fill_buf`]: std::io::BufRead::fill_buf
    pub fn reading_err(&self) -> Option<&Error> {
        match self {
            Utf8BufReaderError::Reading(e) => Some(e),
            _ => None,
        }
    }

    /// Turns this object into [`Error`] if it is a reading error.
    /// 
    /// This function consumes `self`.
    /// 
    /// [`Error`]: std::io::Error
    pub fn into_reading_err(self) -> Option<Error> {
        match self {
            Utf8BufReaderError::Reading(e) => Some(e),
            _ => None,
        }
    }
}

impl std::fmt::Display for Utf8BufReaderError {
    fn fmt(&self, f: &mut std::fmt::Formatter)
    -> std::fmt::Result {
        match self {
            Utf8BufReaderError::Reading(e) => {
                write!(f, "Utf8ReaderError: {}", e)
            }
            Utf8BufReaderError::Decoding(len) => {
                write!(f, "Utf8ReaderError: Decoding error at {}", len)
            }
        }
    }
}

impl std::error::Error for Utf8BufReaderError {}

/// A struct that turns a [`BufRead`] object into a stream of [`char`]s
///     using UTF-8 decoding.
/// 
/// A [`Read`] object can be regarded as a stream of [`u8`]s
///     (via [`Read::bytes`] and [`Iterator::map`]).
/// If the stream of [`u8`]s is a result of UTF-8 encoding,
///     it can be decoded into a stream of [`char`]s.
/// [`Utf8BufReaderStream`] is created for this purpose,
///     but it works with [`BufRead`] instead of [`Read`] because
///     [`BufRead`]'s interface offers higher efficiency, and
///     any [`Read`] object can be turned into a [`BufRead`] object
///     via [`BufReader`].
/// 
/// Iterating through [`char`]s in a text file can be done as follows:
/// 
/// ```no_run
/// use std::fs::File;
/// use std::io::BufReader;
/// use reword::io::Utf8BufReaderStream;
///
/// let f = File::open("foo.txt").unwrap();
/// let buf_size: usize = 1048576;
/// let r = BufReader::with_capacity(buf_size, f);
/// let stream = Utf8BufReaderStream::new(r);
/// for c in stream {
///     // Do something with c
/// }
/// ```
/// 
/// *Note:
///     [`read_utf8_stream`] is a provided function that
///     does exactly this.*
/// 
/// # Error probing
/// 
/// If an error is raised during the read operation of the underlying
///     [`BufRead`] object,
///     [`next`] will return [`None`], and the error will be stored in
///     the public field [`err`].
/// 
/// [`BufRead`]: std::io::BufRead
/// [`Read`]: std::io::Read
/// [`Read::bytes`]: std::io::Read::bytes
/// [`BufReader`]: std::io::BufReader
/// [`Error`]: std::io::Error
/// [`next`]: Utf8BufReaderStream::next
/// [`err`]: Utf8BufReaderStream::err
pub struct Utf8BufReaderStream<R>
where R: BufRead {
    //  Underlying `BufRead` object.
    input: R,
    //  The number of bytes in the underlying input buffer that
    //      have been successfully parsed.
    //  `input_consumed` may be smaller than the length of the input buffer
    //      by at most `MIN_BUFFER_SIZE - 1`.
    input_consumed: usize,
    //  Iterator producing output characters that come from
    //      the main input buffer minus that part needs to be pulled
    //      to parse leftover_input.
    output_it: Chars<'static>,
    //  `active_it` is the first iterator that `next` will pull from.
    //  `active_it` will be set to `output_it` after
    //      `leftover_output_it` finishes iterating.
    //  This is an optimization strategy based on the assumption that
    //      `output_it` generally has a lot more elements than
    //      `leftover_output_it`.
    active_it: Chars<'static>,
    //  Copy of the part of the main input buffer that could not be parsed.
    leftover_input: Vec<u8>,
    //  Iterator producing output characters that come from
    //      `leftover_input` plus the shortest portion of the input buffer
    //      that permits successful parsing.
    leftover_output_it: Chars<'static>,
    //  Internal state that keeps track of whether `leftover_output_it` is
    //      being pulled by `next` or not. 
    check_leftover: bool,
    //  Number of bytes that have been successfully decoded
    //      since the creation of `Utf8BufReaderStream`.
    consumed: usize,

    /// Stores an error that is raised during a call to [`next`].
    /// 
    /// [`Utf8BufReaderStream`] will set `err` to a new value of the form
    ///     [`Some`]`(e)` if an error is raised during a call to [`next`],
    ///     where the type of `e` is [`Utf8BufReaderError`].
    /// [`Utf8BufReaderStream`] does not read from this field,
    ///     so the user is free to read and write to it.
    /// 
    /// Checking the value of `err` when [`next`] returns [`None`] is
    ///     the recommended way to detect the error
    ///     even though `err` might be set during a [`next`] call that
    ///     returns [`Some`] value.
    /// 
    /// # Example
    /// 
    /// ```
    /// use std::io::{BufReader, ErrorKind};
    /// use reword::io::*;
    /// let s = "Hello, world!🙂"; // The last character occupies 4 bytes.
    /// let mut bytes = s.as_bytes().to_vec();
    /// bytes.pop(); // This breaks the last character.
    /// let mut stream = Utf8BufReaderStream::new(
    ///     BufReader::new(bytes.as_slice())
    /// );
    /// let decoded: String = stream.by_ref().collect();
    /// 
    /// // stream doesn't produce the broken character.
    /// assert_eq!(decoded.as_str(), "Hello, world!");
    /// 
    /// // stream.err is public. We can take it out.
    /// let err = stream.err.take();
    ///
    /// // There is an error (caused by the broken character).
    /// assert!(err.is_some());
    ///
    /// // We can check that the error was a decoding error that was triggered
    /// // by an attempt to decode bytes starting at offset 13 in the input
    /// // stream.
    /// assert_eq!(err.unwrap().decoding_err(), Some(13));
    /// 
    /// // stream.decoded_len() will return the same number.
    /// assert_eq!(stream.decoded_len(), 13);
    /// ```
    /// 
    /// [`next`]: Utf8BufReaderStream::next
    pub err: Option<Utf8BufReaderError>,
}

//  Source of empty `Chars` objects.
static EMPTY_STR: &str = "";

impl<R> Utf8BufReaderStream<R>
where R: BufRead {
    /// Creates [`Utf8BufReaderStream`] from a [`BufRead`] object.
    /// 
    /// *Note:
    ///     the [`BufRead`] object should have an underlying buffer
    ///     of length at least [`MIN_BUFFER_SIZE`] to guarantee
    ///     successful operations.*
    /// 
    /// [`BufRead`]: std::io::BufRead
    pub fn new(input: R) -> Self {
        Self {
            input,
            input_consumed: 0,
            output_it: EMPTY_STR.chars(),
            active_it: EMPTY_STR.chars(),
            leftover_input: Vec::with_capacity(6),
            leftover_output_it: EMPTY_STR.chars(),
            check_leftover: false,
            consumed: 0,
            err: None,
        }
    }

    /// Gets a reference to the underlying [`BufRead`] object.
    /// 
    /// [`BufRead`]: std::io::BufRead
    pub fn get_ref(&self) -> &R {
        &self.input
    }

    /// Gets a mutable reference to the underlying [`BufRead`] object.
    /// 
    /// [`BufRead`]: std::io::BufRead
    pub fn get_mut(&mut self) -> &mut R {
        &mut self.input
    }

    /// Destroys this [`Utf8BufReaderStream`],
    ///     returning the underlying [`BufRead`] object.
    /// 
    /// Note that subsequent reading from the returned [`BufRead`] object
    ///     may lead to some data loss because
    ///     [`Utf8BufReaderStream`] caches some data read from
    ///     the underlying [`BufRead`] object
    ///     before parsing and returning the result in [`next`].
    /// 
    /// [`next`]: Utf8BufReaderStream::next
    pub fn into_inner(self) -> R {
        self.input
    }

    //  - Puts all the unparsable part of the input buffer into
    //      `leftover_input`.
    //  - Pulls more input.
    //  - Parses `leftover_input` and the new input.
    //
    //  In the end, `leftover_output_it` and `output_it` will be set
    //      to iterate over the results of parsing
    //      `leftover_input` and the input buffer.
    //  `check_leftover` will be set to `true` if
    //      `leftover_output_it` is not empty.
    //  `input_consumed` will be set to the number of bytes of the input buffer
    //      that have been successfully parsed.
    fn fill_buf(&mut self) -> Result<()> {
        self.input.consume(self.input_consumed);
        let mut input_buf = self.input.fill_buf()?;
        let leftover_len = input_buf.len();
        // If leftover_len < 4, we store it in leftover_input.
        if leftover_len < 4 {
            // Clone input_buf to leftover_input.
            unsafe {
                self.leftover_input.set_len(leftover_len);
            }
            self.leftover_input.copy_from_slice(input_buf);

            // Pull more input now.
            self.input.consume(leftover_len);
            input_buf = self.input.fill_buf()?;

            // Move up to 3 bytes from the beginning of input to the end of
            // leftover_input to make sure that a part of leftover_input can be
            // decoded. 
            let head_len = std::cmp::min(input_buf.len(), 3);
            self.leftover_input.extend_from_slice(&input_buf[..head_len]);

            // Parse leftover_input.
            let (s, consumed) = Self::parse_bytes_to_str(
                self.leftover_input.as_slice()
            );
            self.consumed += consumed;
            self.leftover_output_it = unsafe {
                std::mem::transmute::<_, _>(s.chars())
            };

            // Remove bytes from input that were decoded
            // together with leftover_input.
            if consumed > leftover_len {
                self.input.consume(consumed - leftover_len);
            } else if consumed < leftover_len {
                // Some part of leftover_input cannot be decoded.
                // This must be due to invalid UTF-8 bytes.
                self.err = Some(Utf8BufReaderError::Decoding(self.consumed));
            }
            input_buf = self.input.fill_buf()?;
            self.check_leftover = true;
        }

        // Parse input_buf.
        let (s, consumed) = Self::parse_bytes_to_str(input_buf);
        self.consumed += consumed;
        self.output_it = unsafe {
            std::mem::transmute::<_, _>(s.chars())
        };

        if input_buf.len() > consumed + 3 {
            // If the leftover (undecoded) part of input_buf has length 4 or
            // more, there must be invalid UTF-8 bytes.
            self.err = Some(Utf8BufReaderError::Decoding(self.consumed));
        }
        self.input_consumed = consumed;
        Ok(())
    }

    //  Parses an array of bytes as a `&str` and
    //      returns the number of bytes parsed.
    fn parse_bytes_to_str(bytes: &[u8]) -> (&str, usize) {
        match std::str::from_utf8(bytes) {
            Ok(s) => {
                (s, bytes.len())
            }
            Err(err) => {
                let bound = err.valid_up_to();
                (
                    unsafe {
                        std::str::from_utf8_unchecked(&bytes[..bound])
                    },
                    bound
                )
            }
        }
    }

    /// Returns the number of bytes that have been successfully decoded.
    /// 
    /// The returned number may include input bytes corresponding to
    ///     characters that have not been returned by [`next`].
    /// This is because decoding is done in batches.
    /// Therefore, calling `decoded_len` is generally not meaningful
    ///     until after [`next`] returns [`None`],
    ///     in which case the return value of `decoded_len` is precisely
    ///     the offset into the original input stream
    ///     where parsing error occurs.
    /// 
    /// [`next`]: Utf8BufReaderStream::next
    pub fn decoded_len(&self) -> usize {
        self.consumed
    }

}

impl<R> Iterator for Utf8BufReaderStream<R>
where R: BufRead {
    type Item = char;

    /// Returns the next [`char`] from decoding the byte stream given by
    /// the underlying `BufRead` object.
    /// 
    /// If an error occurs, [`None`] will be returned, and
    ///     [`err`] will be set to [`Some`]`(e)` where
    ///     `e` has type [`Utf8BufReaderError`].
    /// 
    /// [`err`] may also be set when `next` returns [`Some`] value,
    ///     but it is not useful to inspect `err` before
    ///     `next` returns [`None`].
    /// 
    /// [`err`]: Utf8BufReaderStream::err
    #[inline(always)]
    fn next(&mut self) -> Option<char> {
        //  Pulling from `active_it` is sequenced first because
        //      it is in the hot code path.
        if let Some(c) = self.active_it.next() {
            return Some(c);
        }
        //  The first time `next` is called after
        //      `active_it` runs out of elements
        //      is when we need to pull more data into the input buffer.
        if !self.check_leftover {
            if let Err(e) = self.fill_buf() {
                self.err = Some(Utf8BufReaderError::Reading(e));
                return None;
            }
        }
        //  Check `leftover_output_it` before `output_it`.
        if let Some(c) = self.leftover_output_it.next() {
            return Some(c);
        }
        //  Once `leftover_output_it` runs out of elements,
        //      `output_it` will be pulled.
        //  However, since pulling from `output_it` is in the hot code path,
        //      we move it to `active_it` instead.
        self.active_it = std::mem::replace(
            &mut self.output_it,
            EMPTY_STR.chars()
        );
        //  We also set `check_leftover` to `false` because
        //      once `active_it` finishes iterating,
        //      we will need to pull in more input.
        self.check_leftover = false;

        //  At this point, we try to pull from `active_it`.
        if let Some(c) = self.active_it.next() {
            return Some(c);
        }
        //  If `active_it` doesn't have any elements at this point,
        //      it means the input buffer minus the beginning part
        //      that was taken for parsing `leftover_input`
        //      cannot be parsed to yield any output characters.
        //  If this unparsable part is not empty,
        //      it should become the new `leftover_input`.
        //  Otherwise, we must have exhausted the input stream.
        if let Err(e) = self.fill_buf() {
            self.err = Some(Utf8BufReaderError::Reading(e));
            return None;
        }
        self.leftover_output_it.next()
    }

}

#[cfg(test)]
mod test {
    use super::*;

    use std::fs;
    use std::io::BufReader;

    #[test]
    fn test_read_utf8_stream() {
        static TEST_PARAMETERS: &[(&str, &[usize])] = &[
            ("test_data/utf8_all_chars.txt", &[
                0, 16 << 10, usize::MAX,
            ]),
        ];
    
        for &(file_name, max_buffer_sizes) in TEST_PARAMETERS.iter() {
            println!("Testing: file_name = {}", file_name);
            for &max_buffer_size in max_buffer_sizes.iter() {
                println!("         max_buffer_size = {}", max_buffer_size);
                let s = fs::read_to_string(file_name).
                    expect("Failed to read/decode input");
                let builtin_it = s.chars();

                let our_it = read_utf8_stream(file_name, max_buffer_size).
                    expect("Failed to read input");

                assert!(builtin_it.eq(our_it));
            }
        }
    }

    #[test]
    fn test_utf8_buf_reader_stream() {
        static TEST_PARAMETERS: &[usize] = &[
            4, 5, 6, 7, 8,
            58, 59, 60, 61, 62, 63, 63, 64, 66, 67,
            1000,
        ];

        // s has length 62.
        let mut s: String =
            ('0'..='9').chain('A'..='Z').chain('a'..='z').collect();

        // Push a smiley to s. Now s has length 66 (in bytes).
        s.push('\u{1f601}');

        let bytes = s.clone().into_bytes();
        println!("Testing: valid UTF-8");
        for &max_buffer_size in TEST_PARAMETERS.iter() {
            println!("         max_buffer_size = {}", max_buffer_size);
            let buf_reader = BufReader::with_capacity(
                max_buffer_size,
                bytes.as_slice()
            );
            let mut stream = Utf8BufReaderStream::new(buf_reader);
            let result = stream.by_ref().collect::<String>();
            assert_eq!(result, s);
            // err should not be set.
            assert!(stream.err.is_none());
        }

        let mut bytes = s.clone().into_bytes();
        // Now, remove the last byte from the smiley code.
        bytes.pop();
        // The decoded result should lose a whole character.
        // We prepare s similarly for comparison.
        s.pop();

        println!("Testing: invalid UTF-8");
        for &max_buffer_size in TEST_PARAMETERS.iter() {
            println!("         max_buffer_size = {}", max_buffer_size);
            let buf_reader = BufReader::with_capacity(
                max_buffer_size,
                bytes.as_slice()
            );
            let mut stream = Utf8BufReaderStream::new(buf_reader);
            let result = stream.by_ref().collect::<String>();
            assert_eq!(result, s);
            // err should be set.
            assert!(stream.err.is_some());
            // The decoding error happened at offset 62.
            assert_eq!(stream.err.as_ref().unwrap().decoding_err(), Some(62));
        }
    }
}
