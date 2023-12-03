# Day 2

[Link to day 2](https://adventofcode.com/2023/day/2)

## Notes

The trick to this day 3 things. First, to utilize repeated string splitting in
order to parse the input effectively. To complete this, I defined
`String.spanWithout` and `Substring.spanWithout` to make splitting strings or
substrings to pairs of substrings easy. Second, to utilize folds over lists of
`RawReveal` to accumulate values to a single `RawReveal`. And third, to use a
language feature of lean called subtypes. Since lean is a dependently-typed
programming language validations, types, and proofs of valid types can be used
as first class members. The subtypes allow for refinement of types allowing for
easy construction of valid `Reveal` structs. A fold over the validations can
determine if any game was invalid.

