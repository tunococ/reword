// diff module

use std::cmp::min;
use std::mem::size_of;

pub trait BufferBounded {
    /// Returns the smaller value of the size of the object and the size of the buffer.
    fn get_buffer_bound(&self, buffer_size: usize) -> usize;
}

pub struct Change<Value: BufferBounded> {
    pub start: usize,
    pub length: usize,
    pub new_value: Value,
}

pub type Diff<Value> = Vec<Change<Value>>;

impl<T> BufferBounded for Vec<T> {
    fn get_buffer_bound(&self, buffer_size: usize) -> usize {
        min(self.len() * size_of::<T>(), buffer_size)
    }
}

