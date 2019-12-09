//! Container types that asynchronously return ownership of a value to another context upon exiting
//! scope.
//!
//! This crate provides [`VisitingRef`] and [`VisitingMut`], two container types that effectively
//! allow for safe "borrowing" of values through temporary transference of ownership between two
//! separate contexts. These types wrap a given value, only allowing a reference to the value to be
//! taken while the container is active. Upon exiting scope, the owned value is automatically sent
//! back to another context asynchronously.
//!
//! # Usage
//!
//! A [`VisitingRef`] or [`VisitingMut`] is created from an existing value using either
//! [`VisitingRef::new`] or [`VisitingMut::new`], respectively. This returns a tuple with the
//! [`VisitingRef`]/[`VisitingMut`] instance and a [`Return`] future that resolves back to the
//! original value once the [`VisitingRef`]/[`VisitingMut`] is dropped.
//!
//! ```
//! use visiting_ref::VisitingMut;
//!
//! struct Foo {
//!     bar: i32,
//! }
//!
//! let foo = Foo { bar: 12 };
//!
//! let (wrapped_foo, foo_return) = VisitingMut::new(foo);
//! ```
//!
//! The container can then be moved around as needed. The value it contains can be accessed by way
//! of the [`Deref`] trait, with mutable access available for [`VisitingMut`] instances by way of
//! the [`DerefMut`] trait.
//!
//! ```
//! # use visiting_ref::VisitingMut;
//! # struct Foo { bar: i32 }
//! # let (wrapped_foo, foo_return) = VisitingMut::new(Foo { bar: 12 });
//! // `wrapped_foo` is still a `VisitingMut`, but we can access `bar` and other fields
//! // directly.
//! let bar = wrapped_foo.bar;
//! assert_eq!(bar, 12);
//!
//! // Since `wrapped_foo` is a `VisitingMut`, mutable access is also possible.
//! let mut wrapped_foo = wrapped_foo;
//! wrapped_foo.bar = 21;           // Specific fields can be overwritten...
//! *wrapped_foo = Foo { bar: 42 }; // ...as well as the entire `Foo` struct value.
//! ```
//!
//! When the container is dropped, its value is automatically sent back along an asynchronous
//! channel to the [`Return`] future, which will output the value once it is received.
//!
//! ```
//! # use visiting_ref::VisitingMut;
//! # struct Foo { bar: i32 }
//! # let (wrapped_foo, foo_return) = VisitingMut::new(Foo { bar: 42 });
//!
//! fn use_wrapped_foo(wrapped_foo: VisitingMut<Foo>) {
//!     // `wrapped_foo` is used in this context and then goes out of scope, sending the value
//!     // to the `foo_return` future.
//! }
//!
//! use_wrapped_foo(wrapped_foo);
//!
//! # futures_executor::block_on(async move {
//! // Once `foo_return` resolves, it will output the same wrapped `Foo` value that we accessed
//! // and modified previously.
//! let foo = foo_return.await;
//! assert_eq!(foo.bar, 42);
//! # });
//! ```
//!
//! # `no_std` Support
//!
//! This crate does not require [`std`], but it does require [`alloc`] due to the use of [`futures`
//! oneshot channels]. No features need to be disabled for use with `no_std` crates.
//!
//! # Implementation Notes
//!
//! It is not possible to unwrap a [`VisitingRef`] or [`VisitingMut`] into its contained value type.
//! Direct ownership of the contained value is always passed back through the [`Return`] future when
//! the container is dropped.
//!
//! The [`Return`] future can be dropped before the corresponding [`VisitingRef`] or [`VisitingMut`]
//! is dropped. If this occurs, dropping a [`VisitingRef`] or [`VisitingMut`] will also drop the
//! contained value.
//!
//! # Examples
//!
//! One could implement a simple object pool system that automatically returns objects to the pool
//! once the [`VisitingRef`] goes out of scope and the object is returned.
//!
//! ```
//! use futures_channel::oneshot::{channel, Sender};
//! use futures_util::lock::Mutex;
//! use std::{collections::VecDeque, error::Error, sync::Arc};
//! use tokio::runtime::Runtime;
//! use visiting_ref::VisitingMut;
//!
//! /// Core object pool data. For simplicity in this example, access to this data is
//! /// synchronized via mutex lock.
//! struct PoolData<T>
//! where
//!     T: Send + 'static,
//! {
//!     /// Unused objects.
//!     objects: Vec<T>,
//!     /// Notification senders for async contexts that are waiting for an object.
//!     waiting_queue: VecDeque<Sender<T>>,
//! }
//!
//! /// A simple, inefficient object pool.
//! pub struct Pool<T>
//! where
//!     T: Send + 'static,
//! {
//!     data: Arc<Mutex<PoolData<T>>>,
//! }
//!
//! impl<T> Pool<T>
//! where
//!     T: Send + 'static,
//! {
//!     /// Initializes the pool from a predefined array of some type `T`.
//!     pub fn new(objects: Vec<T>) -> Self {
//!         Self {
//!             data: Arc::new(Mutex::new(PoolData {
//!                 objects,
//!                 waiting_queue: VecDeque::new(),
//!             })),
//!         }
//!     }
//!
//!     /// Asynchronously acquires an object from this pool, waiting if no objects are
//!     /// currently
//!     /// available.
//!     pub async fn get(&self) -> VisitingMut<T> {
//!         // Attempt to remove the next available item from the pool.
//!         let mut guard = self.data.lock().await;
//!         let item = match guard.objects.pop() {
//!             Some(item) => {
//!                 drop(guard);
//!                 item
//!             }
//!
//!             None => {
//!                 // No item is currently available, so put this future into a waiting queue
//!                 // to receive an item once one becomes available again.
//!                 let (sender, receiver) = channel();
//!                 guard.waiting_queue.push_back(sender);
//!                 drop(guard);
//!
//!                 receiver.await.unwrap()
//!             }
//!         };
//!
//!         // Wrap the pool item in a `VisitingMut`. This returns the wrapped item and a future
//!         // that will resolve back to the pool item once the `VisitingMut` is dropped.
//!         let (item, item_return) = VisitingMut::new(item);
//!
//!         // Spawn a future to either return the item to the pool when it is done or pass it
//!         // along directly to another future that's waiting for a pooled item to become
//!         // available.
//!         let data_clone = Arc::clone(&self.data);
//!         tokio::spawn(async move {
//!             let mut item_opt = Some(item_return.await);
//!             let mut guard = data_clone.lock().await;
//!
//!             while let Some(item) = item_opt.take() {
//!                 if let Some(sender) = guard.waiting_queue.pop_front() {
//!                     // Failure to send the value on a waiting channel means that the
//!                     // receiving end was closed, so ignore and continue.
//!                     if let Err(item) = sender.send(item) {
//!                         item_opt = Some(item);
//!                     }
//!                 } else {
//!                     guard.objects.push(item);
//!                 }
//!             }
//!         });
//!
//!         item
//!     }
//! }
//!
//! fn main() -> Result<(), Box<dyn Error>> {
//!     let mut rt = Runtime::new()?;
//!     rt.block_on(async {
//!         let pool = Pool::new(vec![1, 2]);
//!
//!         // Our `Pool::get` method always returns the item at the end of the pool first (in
//!         // this case, it will be the `2` value we provided during initialization).
//!         let mut x = pool.get().await;
//!         assert_eq!(*x, 2);
//!         let y = pool.get().await;
//!         assert_eq!(*y, 1);
//!
//!         // We can modify an item, so the next call that retrieves the same item later will
//!         // see the updated value.
//!         *x = 5;
//!
//!         // Dropping the `VisitingMut` sets it up to be requeued.
//!         drop(x);
//!
//!         // Fetch the item we just released. Note that since the requeueing is asynchronous,
//!         // the item isn't guaranteed to be back in the pool yet, but since the pool was
//!         // empty, the following code will wait for the item to become available if
//!         // necessary.
//!         let a = pool.get().await;
//!         assert_eq!(*a, 5);
//!     });
//!
//!     Ok(())
//! }
//! ```
//!
//! [`VisitingRef`]: struct.VisitingRef.html
//! [`VisitingMut`]: struct.VisitingMut.html
//! [`std`]: https://doc.rust-lang.org/std/
//! [`alloc`]: https://doc.rust-lang.org/alloc/
//! [`futures` oneshot channels]: https://docs.rs/futures-channel/0.3/futures_channel/oneshot/fn.channel.html
//! [`VisitingRef::new`]: struct.VisitingRef.html#method.new
//! [`VisitingMut::new`]: struct.VisitingMut.html#method.new
//! [`Return`]: struct.Return.html
//! [`Deref`]: https://doc.rust-lang.org/std/ops/trait.Deref.html
//! [`DerefMut`]: https://doc.rust-lang.org/std/ops/trait.DerefMut.html

#![no_std]

extern crate alloc;

use alloc::fmt;
use core::{
    mem::ManuallyDrop,
    ops::{Deref, DerefMut},
    pin::Pin,
    ptr,
};
use futures_channel::oneshot::{channel, Receiver, Sender};
use futures_core::{
    future::Future,
    ready,
    task::{Context, Poll},
};

/// Container that automatically returns ownership of a value to another async context upon exiting
/// scope, allowing immutable access to the value while active.
///
/// `VisitingRef` implements [`Deref`] to allow for immutable access to the wrapped value, either
/// explicitly using the unary `*` operator or implicitly by the compiler under various
/// circumstances. More information can be found in the [`Deref`] trait documentation.
///
/// For mutable value access, see [`VisitingMut`].
///
/// [`Deref`]: https://doc.rust-lang.org/std/ops/trait.Deref.html
/// [`VisitingMut`]: struct.VisitingMut.html
pub struct VisitingRef<T> {
    inner: VisitingInner<T>,
}

impl<T> VisitingRef<T> {
    /// Creates a new `VisitingRef` wrapping the given value, along with a future that resolves back
    /// the wrapped value once the `VisitingRef` is dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// use visiting_ref::VisitingRef;
    ///
    /// # futures_executor::block_on(async move {
    /// let (item, receiver) = VisitingRef::new(5);
    /// assert_eq!(*item, 5);
    ///
    /// drop(item);
    /// let original = receiver.await;
    /// assert_eq!(original, 5);
    /// # });
    /// ```
    pub fn new(value: T) -> (Self, Return<T>) {
        let (sender, receiver) = channel();
        let inner = VisitingInner::new(value, sender);

        (Self { inner }, Return { receiver })
    }
}

impl<T> Deref for VisitingRef<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        &*self.inner.value
    }
}

impl<T> fmt::Debug for VisitingRef<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("VisitingRef")
            .field("value", &self.inner.value)
            .finish()
    }
}

impl<T> fmt::Display for VisitingRef<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner.value.fmt(f)
    }
}

impl<T> From<VisitingMut<T>> for VisitingRef<T> {
    #[inline]
    fn from(value: VisitingMut<T>) -> Self {
        VisitingMut::downgrade(value)
    }
}

/// Container that automatically returns ownership of a value to another async context upon exiting
/// scope, allowing mutable access to the value while active.
///
/// `VisitingMut` implements both [`Deref`] and [`DerefMut`] to allow for immutable or mutable
/// access to the wrapped value, either explicitly using the unary `*` operator or implicitly by the
/// compiler under various circumstances. More information can be found in the [`Deref`] trait and
/// [`DerefMut`] trait documentation.
///
/// `VisitingMut` instances can be permanently downgraded to [`VisitingRef`] using either
/// [`VisitingMut::downgrade`] or the [`From`] trait implementation for [`VisitingRef`]. A
/// [`VisitingRef`] cannot be converted back into a `VisitingMut`.
///
/// [`Deref`]: https://doc.rust-lang.org/std/ops/trait.Deref.html
/// [`DerefMut`]: https://doc.rust-lang.org/std/ops/trait.DerefMut.html
/// [`VisitingRef`]: struct.VisitingRef.html
/// [`VisitingMut::downgrade`]: struct.VisitingMut.html#method.downgrade
/// [`From`]: https://doc.rust-lang.org/std/convert/trait.From.html
pub struct VisitingMut<T> {
    inner: VisitingInner<T>,
}

impl<T> VisitingMut<T> {
    /// Creates a new `VisitingMut` wrapping the given value, along with a future that resolves back
    /// the wrapped value once the `VisitingMut` is dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// use visiting_ref::VisitingMut;
    ///
    /// # futures_executor::block_on(async move {
    /// let (mut item, receiver) = VisitingMut::new(5);
    /// assert_eq!(*item, 5);
    ///
    /// *item = 7;
    ///
    /// drop(item);
    /// let original = receiver.await;
    /// assert_eq!(original, 7);
    /// # });
    /// ```
    pub fn new(value: T) -> (Self, Return<T>) {
        let (sender, receiver) = channel();
        let inner = VisitingInner::new(value, sender);

        (Self { inner }, Return { receiver })
    }

    /// Permanently downgrades a `VisitingMut` into a [`VisitingRef`].
    ///
    /// # Examples
    ///
    /// ```
    /// use visiting_ref::VisitingMut;
    ///
    /// let (mut item, receiver) = VisitingMut::new(5);
    /// assert_eq!(*item, 5);
    ///
    /// *item = 7;
    ///
    /// let item = VisitingMut::downgrade(item);
    /// assert_eq!(*item, 7);
    /// ```
    ///
    /// [`VisitingRef`]: struct.VisitingRef.html
    #[inline]
    pub fn downgrade(value: Self) -> VisitingRef<T> {
        VisitingRef { inner: value.inner }
    }
}

impl<T> Deref for VisitingMut<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        &*self.inner.value
    }
}

impl<T> DerefMut for VisitingMut<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        &mut *self.inner.value
    }
}

impl<T> fmt::Debug for VisitingMut<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("VisitingMut")
            .field("value", &self.inner.value)
            .finish()
    }
}

impl<T> fmt::Display for VisitingMut<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner.value.fmt(f)
    }
}

/// Future that resolves to the value wrapped by a [`VisitingRef`] or [`VisitingMut`] after the
/// container is dropped.
///
/// Instances of this type are created when using [`VisitingRef::new`] and [`VisitingMut::new`] to
/// create a new wrapped value.
///
/// [`VisitingRef`]: struct.VisitingRef.html
/// [`VisitingMut`]: struct.VisitingMut.html
/// [`VisitingRef::new`]: struct.VisitingRef.html#method.new
/// [`VisitingMut::new`]: struct.VisitingMut.html#method.new
pub struct Return<T> {
    /// Receiver part of the channel on which the value is being returned.
    receiver: Receiver<T>,
}

impl<T> Future for Return<T> {
    type Output = T;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<T> {
        // The implementation of `VisitingInner` guarantees that the channel is never closed before
        // the value is sent back, so we can safely `unwrap` the receiver result (receiver errors
        // only occur if the channel is closed early) so that the caller doesn't have to worry about
        // it.
        Poll::Ready(
            ready!(Pin::new(&mut self.receiver).poll(cx))
                .expect("VisitingRef and VisitingMut return channel should never close early"),
        )
    }
}

/// Shared container for `VisitingRef` and `VisitingMut`.
struct VisitingInner<T> {
    /// Wrapped value.
    value: ManuallyDrop<T>,
    /// Sender part of the channel on which the wrapped value is returned when this object is
    /// dropped.
    sender: ManuallyDrop<Sender<T>>,
}

impl<T> VisitingInner<T> {
    /// Creates a new inner container for `VisitingRef` and `VisitingMut`.
    fn new(value: T, sender: Sender<T>) -> Self {
        Self {
            value: ManuallyDrop::new(value),
            sender: ManuallyDrop::new(sender),
        }
    }
}

impl<T> Drop for VisitingInner<T> {
    fn drop(&mut self) {
        let (value, sender) = unsafe {
            (
                ManuallyDrop::into_inner(ptr::read(&self.value)),
                ManuallyDrop::into_inner(ptr::read(&self.sender)),
            )
        };

        // Sending the value back will fail if the receiver is dropped. Since we have no place to
        // put the value in this situation, simply let the value drop as well.
        sender.send(value).unwrap_or_else(|_| ());
    }
}