# Day 1

[Link to Day 1](https://adventofcode.com/2023/day/1)

## Notes

Trick to complete this day is pattern matching in the `getParsedDigit` and
`getDigit` functions and treating the initial List of Characters in each line
as a pseudo comonad

By lifting an expected List of Characters into the comonad realm with
`List.duplicate` then passing the `getDigit` and `getParsedDigit` functions
around from both the left and the right is made trivial as the `List (List
Char)` can be reordered
