/// Macros to give syntactic sugar for zipWith pattern and variatns.
///
/// ```ignore
/// use crate::spartan::zip_with;
/// use itertools::Itertools as _; // we use zip_eq to zip!
/// let v = vec![0, 1, 2];
/// let w = vec![2, 3, 4];
/// let y = vec![4, 5, 6];
///
/// // Using the `zip_with!` macro to zip three iterators together and apply a closure
/// // that sums the elements of each iterator.
/// let res = zip_with!((v.iter(), w.iter(), y.iter()), |a, b, c| a + b + c)
///     .collect::<Vec<_>>();
///
/// println!("{:?}", res); // Output: [6, 9, 12]
/// ```

#[macro_export]
macro_rules! zip_with {
    (($e:expr $(, $rest:expr)*), $($move:ident)? |$($i:ident),+ $(,)?| $($work:tt)*) => {{
        $crate::zip_all!(($e $(, $rest)*))
            .map($($move)? |$crate::nested_idents!($($i),+)| {
                $($work)*
            })
    }};
}

/// Like `zip_with` but call `iter()` on each input to produce the iterators.
#[macro_export]
macro_rules! zip_with_iter {
    (($e:expr $(, $rest:expr)*), $($move:ident)? |$($i:ident),+ $(,)?| $($work:tt)*) => {{
        $crate::zip_with_fn!(iter, ($e $(, $rest)*), $($move)? |$($i),+| $($work)*)
    }};
}

/// Like `zip_with` but call `par_iter()` on each input to produce the iterators.
#[macro_export]
macro_rules! zip_with_par_iter {
    (($e:expr $(, $rest:expr)*), $($move:ident)? |$($i:ident),+ $(,)?| $($work:tt)*) => {{
        $crate::zip_with_fn!(par_iter, ($e $(, $rest)*), $($move)? |$($i),+| $($work)*)
    }};
}

/// Like `zip_with` but call `into_iter()` on each input to produce the iterators.
#[macro_export]
macro_rules! zip_with_into_iter {
    (($e:expr $(, $rest:expr)*), $($move:ident)? |$($i:ident),+ $(,)?| $($work:tt)*) => {{
        $crate::zip_with_fn!(into_iter, ($e $(, $rest)*), $($move)? |$($i),+| $($work)*)
    }};
}

/// Like `zip_with` but call `into_par_iter()` on each input to produce the iterators.
#[macro_export]
macro_rules! zip_with_into_par_iter {
    (($e:expr $(, $rest:expr)*), $($move:ident)? |$($i:ident),+ $(,)?| $($work:tt)*) => {{
     $crate::zip_with_fn!(into_par_iter, ($e $(, $rest)*), $($move)? |$($i),+| $($work)*)
    }};
}

/// General utility macro for `zip_with` variants where iterator-producer and optional post-zip function can be
/// specified.
#[macro_export]
macro_rules! zip_with_fn {
    ($f:ident, ($e:expr $(, $rest:expr)*), [$worker:ident] $($move:ident)?, |$($i:ident),+ $(,)?|  $($work:tt)*) => {{
        $crate::zip_all_with_fn!($f, ($e $(, $rest)*))
            .$worker($($move)? |$crate::nested_idents!($($i),+)| {
                $($work)*
            })
    }};
    ($f:ident, ($e:expr $(, $rest:expr)*), $($move:ident)? |$($i:ident),+ $(,)?| $($work:tt)*) => {{
        $crate::zip_all_with_fn!($f, ($e $(, $rest)*))
            .map($($move)? |$crate::nested_idents!($($i),+)| {
                $($work)*
            })
    }};
}

/// Like `zip_with` but use `for_each` instead of `map`.
#[macro_export]
macro_rules! zip_with_for_each {
    (($e:expr $(, $rest:expr)*), $($move:ident)? |$($i:ident),+ $(,)?| $($work:tt)*) => {{
        $crate::zip_all!(($e $(, $rest)*))
            .for_each($($move)? |$crate::nested_idents!($($i),+)| {
                $($work)*
            })
    }};
}

/// Like `zip_with` but use `flat_map` instead of `map`.
#[macro_export]
macro_rules! zip_with_flat_map {
    (($e:expr $(, $rest:expr)*), $($move:ident)? |$($i:ident),+ $(,)?| $($work:tt)*) => {{
        $crate::zip_all!(($e $(, $rest)*))
            .flat_map($($move)? |$crate::nested_idents!($($i),+)| {
                $($work)*
            })
    }};
}

/// Like `zip_with` but call `iter()` on each input to produce the iterators, and apply `flat_map` instead of `map` after
/// zipping.
#[macro_export]
macro_rules! zip_with_iter_flat_map {
    (($e:expr $(, $rest:expr)*), $($move:ident)? |$($i:ident),+ $(,)?| $($work:tt)*) => {{
        $crate::zip_with_fn!(iter, ($e $(, $rest)*), [flat_map], $($move)?  |$($i),+| $($work)*)
    }};
}

/// Like `zip_with` but call `par_iter_mut()` on each input to produce the iterators, and apply `for_each` instead of
/// `map` after zipping.
#[macro_export]
macro_rules! zip_with_par_iter_mut_for_each {
    (($e:expr $(, $rest:expr)*), $($move:ident)? |$($i:ident),+ $(,)?| $($work:tt)*) => {{
        $crate::zip_with_fn!(par_iter_mut, ($e $(, $rest)*), [for_each], $($move)? |$($i),+| $($work)*)
    }};
}

// Fold-right like nesting pattern for expressions a, b, c, d => (a, (b, (c, d)))
#[doc(hidden)]
#[allow(unused_macros)]
#[macro_export]
macro_rules! nested_tuple {
    ($a:expr, $b:expr) => {
        ($a, $b)
    };
    ($first:expr, $($rest:expr),+) => {
        ($first, $crate::nested_tuple!($($rest),+))
    };
}

// Same as the above for idents
#[doc(hidden)]
#[allow(unused_macro_rules)]
#[macro_export]
macro_rules! nested_idents {
    ($a:ident, $b:ident) => {
        ($a, $b)
    };
    ($first:ident, $($rest:ident),+) => {
        ($first, $crate::nested_idents!($($rest),+))
    };
}

// Fold-right like zipping
#[doc(hidden)]
#[macro_export]
macro_rules! zip_all {
    (($e:expr,)) => {
        $e
    };
    (($first:expr, $second:expr $(, $rest:expr)*)) => {
        ($first.zip_eq($crate::zip_all!(($second, $( $rest),*))))
    };
}

/// Like `zip_all` but with specified function to produce the iterators
#[macro_export]
macro_rules! zip_all_with_fn {
    ($f:ident, ($e:expr,)) => {
        $e.$f()
    };
    ($f:ident, ($first:expr, $second:expr $(, $rest:expr)*)) => {
        ($first.$f().zip_eq($crate::zip_all_with_fn!($f, ($second, $( $rest),*))))
    };
}
