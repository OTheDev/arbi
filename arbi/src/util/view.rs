/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::util::ArbiLikeArray;
use crate::{Arbi, Assign, Digit};

pub(crate) struct ArbiLikeView<'a> {
    pub(crate) vec: &'a [Digit],
    pub(crate) neg: bool,
}

// TODO: trait for copied methods?
impl ArbiLikeView<'_> {
    #[allow(dead_code)]
    #[inline(always)]
    pub(crate) fn size(&self) -> usize {
        self.vec.len()
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub(crate) fn is_negative(&self) -> bool {
        self.neg
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub(crate) fn is_zero(&self) -> bool {
        self.vec.is_empty()
    }
}

impl Assign<ArbiLikeView<'_>> for Arbi {
    #[inline(always)]
    fn assign(&mut self, value: ArbiLikeView) {
        self.assign_slice(value.vec, value.neg);
    }
}

impl Arbi {
    #[allow(dead_code)]
    #[inline(always)]
    pub(crate) fn as_arbi_like_view(&self) -> ArbiLikeView {
        ArbiLikeView {
            vec: &self.vec,
            neg: self.neg,
        }
    }
}

impl<'a, const N: usize> From<&'a ArbiLikeArray<N>> for ArbiLikeView<'a> {
    fn from(arbi_like: &'a ArbiLikeArray<N>) -> Self {
        ArbiLikeView {
            vec: arbi_like.digits(),
            neg: arbi_like.is_negative(),
        }
    }
}

impl<'a> From<&'a Arbi> for ArbiLikeView<'a> {
    fn from(arbi: &'a Arbi) -> Self {
        ArbiLikeView {
            vec: &arbi.vec,
            neg: arbi.is_negative(),
        }
    }
}
