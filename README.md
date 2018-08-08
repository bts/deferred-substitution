# deferred-substitution

An implementation of the formal system from Ben Lippmeier's [Don't Substitute Into Abstractions](http://benl.ouroborus.net/papers/2016-dsim/lambda-dsim-20160328.pdf), using a map instead of an ordered list of substitutions.

From the paper:

> During reduction, by not substituting into abstractions we can retain the names present in the initial expression, and avoid the need to generate new, fresh names.
