# Sorting verification

[Verification catalog](../verification.en.md) | [日本語](sorting.md)

## Shared specification

Source: `LeanExperiments/Verification/Sorting/Spec.lean`

`Correct input output` states that the output is ascending and preserves every input element with its multiplicity. It implies preservation of length, sum, and the occurrence count of each value. A correct nonempty output begins with an input minimum and ends with an input maximum.

When a separate general theorem establishes that an output is a permutation of its input, the shared Boolean checker is equivalent to checking ascendingness alone. This separates each sorting implementation's element-preservation proof from its comparison against the independent specification.

The heap-sort array specification converts arrays to lists and reuses this shared specification.

## Quick sort

### General theorems

- Both recursive and loop-based implementations satisfy `Correct` for every input.
- The partition into values at most the pivot and values above it is a permutation of the input. The proofs establish exact membership and bounds, disjointness, and distribution of the count for any Boolean predicate.
- Separate lemmas show that recursive sorting keeps values on the correct side of the pivot and orders the two outputs.
- The loop-based implementation is proved equal to the recursive one for arbitrary inputs using a task-stack meaning invariant, a termination measure, and VCGen.
- For both implementations, the general permutation theorem reduces success of the shared Boolean checker to ascendingness of the output.

### Finite checks

Specification compliance and agreement with recursive quick sort are checked for the loop implementation. Each result can be extracted as a `Correct` proposition for its domain.

- All 364 inputs of length 0–5 over values 0–2
- All 87,381 inputs of length 0–8 over values 0–3
- All 97,656 inputs of length 0–7 over values 0, 1, 2, `2³²`, and `2⁶⁴−1`
- Sorted, reverse, and other highly unbalanced patterns at lengths 63, 64, 65, 127, 128, 129, 255, 256, 257, 511, 512, and 513, plus 64-bit boundary-value patterns
- Sorted, reverse, all-equal, and periodic inputs at lengths 1,023, 1,024, and 1,025

## Merge sort

### General theorems

- Recursive and loop-based implementations satisfy `Correct` for every input.
- The loop implementation agrees with an adjacent-run merge model. Geometric reduction in the number of runs also proves agreement with a fixed-round model when the input length is at most `2^rounds`.
- The proofs establish agreement between the implementations, uniqueness of a correct ascending result, idempotence, minimum and maximum placement, and that already sorted input is unchanged.
- For both recursive and loop-based implementations, the shared Boolean check succeeds exactly when the output is ascending, by their general permutation theorems.
- For loop-based merge sort, output equality is equivalent to the inputs being permutations of each other. It also preserves length, sum, counts for any Boolean predicate, and order-statistic bounds.

### Finite checks

The loop implementation is checked on sorted, reverse, all-equal, and periodic inputs of lengths 1,023, 1,024, and 1,025. Across sorting implementations, checks also cover representative length-64 patterns, heap-level boundaries from 63 through 513, and 48 64-bit boundary-value patterns at those lengths.

## Heap sort

### General theorems

- The Boolean sorting checker is equivalent to the logical specification of ascending output and element preservation. Any two outputs that pass for the same input are equal.
- The logical max-heap parent-child condition is equivalent to its Boolean checker, and it implies that the root is at least every array element.
- The heap-build specification implies preservation of array length and the sum of natural-number values. Both loop-based and recursive `popMax` return the root and fail exactly on an empty array.
- A generic residual specification for extraction is equivalent to its Boolean checker. An extractor satisfying the contract produces a non-increasing sequence from a max heap and preserves input elements when combined with its remainder. With sufficient fuel, reversing the extraction sequence satisfies the shared sorting specification.
- Extraction sequences from the same heap agree for any two sufficient fuel values. This follows because their reversals both satisfy the shared, unique sorting specification.
- A partial extraction with fuel at most the heap size is a prefix of the completed extraction sequence from the same heap, relating intermediate and final results.
- Two extractors satisfying the residual contract produce the same partial sequence from the same max heap at the same fuel, by combining completed-output uniqueness with the prefix theorem.
- If extraction contracts are proved only up to a size bound, completed sorting outputs still agree within that bound; this composes bounded implementation proofs.
- A correct heap build composes with a size-bounded extraction contract to prove sorting correctness within that bound.
- Under a size-bounded extraction contract, partial runs are prefixes of completed runs, and two implementations agree even at intermediate steps. This applies to bounded proofs such as recursive `popMax` on heaps of length at most nine.
- A size-bounded contract also proves that every partial extraction sequence up to the heap length is descending, by composing completed-run correctness with the prefix theorem.
- Within the same bound, the number of extracted elements equals `fuel`, proving that extraction does not stop early.
- Reversing a partial extraction sequence under a bounded contract satisfies the shared `Ascending` specification, giving a sorted top-`fuel` result.
- By connecting the abstract extraction sequence to `drainRecursive`, its executable partial result is also ascending and has exactly `fuel` elements.
- Resuming a partial drain from a descending accumulator also yields ascending output when every remaining heap value is bounded by the accumulator; the output length is the previous length plus `fuel`.
- The partial `drainRecursive` output and remainder heap together preserve the count of values satisfying any Boolean predicate. This states the partition invariant directly for the output array and unprocessed heap.
- When resuming from an existing accumulator, predicate counts in the prior output and heap are distributed across the resumed output and remainder heap. The proof does not require an ordering condition on the prior output.
- Under a size-bounded extraction contract, partial resumption has a combined general contract for ascending output, the exact number of appended elements, and preservation of any Boolean predicate count. Ordering and element preservation can be checked from the same assumptions.
- For inputs of length at most nine, if recursive heap construction returns a max heap, the recursive sorter is correct for arbitrary natural values. Proving the builder's heap invariant then composes with the existing size-nine extraction contract and general element preservation.
- For length-nine inputs whose root is a maximum value, recursive heap sort is proved correct: the lower subtrees are heapified while the root stays fixed, then the size-nine extraction contract completes the proof. The theorem covers arbitrary values under the root-maximum precondition.
- A unified theorem covers lengths up to nine under the same root-maximum premise; the premise is only needed at length nine because all shorter inputs already have unconditional proofs.
- At length nine, the precondition is weakened further: it is enough that the root dominate its children after processing indices 3, 2, and 1. The subtree heap conditions are proved, so this exposes only the condition needed by the final sift-down.
- A unified theorem covers lengths up to nine under this weaker condition; lengths up to eight remain unconditional, and the root-step condition is only needed at length nine.
- Every value emitted by a partial `drainRecursive` run is at least each value extracted later in the completed run, transferring the top-k property to the recursive implementation.
- Given a max-heap input and a size-bounded extraction contract, the completed `drainRecursive` output is ascending and a permutation of the input.
- The drain proof also supports resumption: if the existing output is descending and every remaining heap value is no greater than its values, the combined result remains a sorted permutation.
- For any extractor, splitting fuel into two stages yields the concatenation of both extracted sequences and the same final remainder as a single run, without assuming an extraction contract.
- `drainRecursive` also composes across stages: append the first stage's extracted values to its accumulator, resume from its remainder heap, and the final output equals a single run.
- Under a size-bounded contract, the partial extracted sequence together with the remainder heap is a permutation of the input; counts for any Boolean predicate are preserved across the two parts.
- Every value in a partial extraction sequence is at least each value appearing later in the completed sequence, establishing a general top-`fuel` property under a size-bounded contract.
- For an extractor with only the element-preservation contract, every partial run preserves the count of values satisfying any Boolean predicate when the extracted prefix and remainder are combined. This general partition invariant does not depend on extraction order or the heap condition.
- For an extractor satisfying the residual contract, the remainder length after any fuel is exactly `input length - fuel`, truncated at zero. This gives an exact bound on extraction progress for every run.
- The same contract proves that the extracted element count is `min fuel input length`: enough fuel processes every element exactly once, while insufficient fuel processes exactly that many.
- The weaker element-preservation and size-decrease contract alone also proves the exact remainder length and extracted count for every fuel, without requiring heap validity or extraction order.
- Recursive heap construction preserves every input element as a permutation for arbitrary inputs, which also implies preservation of array length and the sum of values. This theorem does not establish the max-heap invariant.
- Recursive heap construction produces a max heap from every input and preserves all elements as a permutation. Its invariant states that all parent-child edges at or above the next unprocessed index satisfy the heap condition; each sift-down extends this range toward the root. The independent Boolean checker accepts every constructed heap.
- Recursive `popMax` satisfies root extraction, residual max-heap validity, and residual element preservation for max heaps of any size. Composing these results with the abstract extraction contract proves `Correct` for `heapSortRecursive` on arbitrary input lengths and natural-number values, and its output passes the independent Boolean checker.
- For the recursive sorter at any input length, correctness is equivalent to output ascendingness. The general element-preservation and ascendingness proofs combine into the unrestricted `Correct` theorem. The independent Boolean checker also decides ascendingness exactly for every input.
- For max-heap inputs of length at most nine, recursive heap construction leaves the input unchanged, and the max-heap extraction contract proves that `heapSortRecursive` sorts it correctly.
- For arbitrary input lengths, `heapSortRecursive` preserves the input as a permutation, and therefore preserves array length and the sum of natural-number values. This conservation theorem is separate from and composes with the general sortedness proof.
- For any fuel, heap, and existing output, recursive draining equals the reverse of the abstract maximum-extraction sequence appended to that output. This theorem connects the general extraction specification to the concrete recursive implementation.
- The imperative `siftDown` equals `siftDownRecursive` for every array and root position. This general proof composes the one-step state transition, invariant preservation, the stopping fixed point, and a decreasing measure. It transfers the general recursive sift-down contracts to the loop implementation.
- For any fuel, input array, and root position, fuel-bounded sift-down preserves array length and the element permutation. A general frame theorem proves that it leaves every index above the recursive target unchanged; the verification specification derives list-prefix preservation and permutation preservation of the suffix beginning at the root. The suffix length, sum, and count of elements satisfying any Boolean predicate are preserved; the predicate-count contract is also proved for recursive sift-down. With positive fuel, the resulting root equals the initial largest candidate and therefore dominates both initial children; recursive sift-down has the same domination property. The result equals the input exactly when fuel is zero or the root dominates its existing children. With positive fuel, the root value strictly increases exactly when an in-bounds child initially exceeds it; this also covers root indices outside the array. Any sufficient fuel can be reduced to `values.size - root`, and recursive sift-down is proved equal to this minimum-depth fuel execution.
- Recursive `siftDownRecursive` preserves both array length and the element permutation for every array and root position, and leaves the array unchanged when the left child is out of bounds. The root descent results for five-, six-, seven-, and eight-element arrays, plus child-position descents for six-, seven-, and eight-element arrays, are characterized generally by value comparisons. For eight elements, post-descent subtree conditions are proved at indices 1, 2, and 3. For nine elements, descent results and subtree conditions are proved at indices 1, 2, and 3; processing indices 3, 2, and 1 in heap construction makes both root child subtrees heaps. A successful `popMaxRecursive` reduces the remainder length by exactly one and preserves, as a permutation, every input element except the root. The generic extraction element-preservation contract also yields count preservation for any Boolean predicate across the extracted value and remainder.
- For an arbitrary root, if the input satisfies every parent-child edge whose parent index is greater than that root, the root after recursive sift-down dominates every value in the output subtree. Parent-child edges outside the selected child's subtree are also equivalent before and after descent. These general lemmas separate restoration of the root edge from preservation of edges untouched by the recursive call.
- For any root, if every parent-child edge below it is already a max-heap edge, then sufficient-fuel sift-down makes the entire root subtree a max heap. This proves that recursive `siftDown`, which preserves all parent-child edges outside the root subtree, keeps any max heap valid, and that recursive `popMax` leaves a max heap for inputs of any size.
- `HeapDescendant` can identify which child of a root a strict descendant passes through, and proves that the subtrees of distinct sibling children are disjoint at every depth. These tree-index facts provide shared structure for splitting subtree invariants over array-based heaps.
- The loop-based heap builder equals the recursive builder on arbitrary inputs. A loop invariant preserves the remaining recursive construction, and the general agreement theorem for `siftDown` connects each loop iteration to its recursive counterpart. The loop builder therefore establishes the max-heap property, preserves the input permutation, and passes the independent Boolean checker for every input.
- Loop-based `popMax` equals its recursive counterpart for every array and satisfies the general size and element-preservation contract. Both implementations directly preserve the count of any Boolean classification across the extracted value and remainder. The loop implementation also exposes direct theorems that a max-heap input leaves a max-heap remainder and that the remainder is a permutation of the input with its root removed; the remainder checker accepts it as well.
- On max-heap inputs, recursive and loop-based `popMax` satisfy the maximum-order contract: they fail on empty heaps and otherwise return the root, which bounds every input value, while the remainder preserves the other elements as a permutation.
- Loop-based `heapSort` equals recursive `heapSortRecursive` for arbitrary inputs, using an invariant that relates the remaining iterations to recursive draining. Therefore the loop implementation itself satisfies `Correct` for every input length and value, and passes the independent Boolean checker.
- For both recursive and loop-based implementations, a candidate output equals the implementation result exactly when it satisfies the shared `Correct` specification or passes the independent Boolean checker. Any accepted candidate can therefore be identified as the actual result.
- Loop-based `heapSort` preserves array length, the sum of natural-number values, and the count of elements satisfying any Boolean predicate for arbitrary input lengths and values. The predicate-count theorem directly states element preservation with multiplicity.
- The shared sorting specification proves that mapping a list through any monotone function preserves `Correct`. As a corollary, both loop-based and recursive heap sort commute with mapping through every monotone `f` on arbitrary arrays.
- A general theorem derives commutation between any correct sorter and a monotone map from the shared specification. It is applied to recursive and iterative heap sort, merge sort, and quick sort.
- For any list sorter satisfying the shared specification, permutation-equivalent inputs produce the same output, ascending inputs are unchanged, and sorting twice is idempotent. These laws are applied to the recursive and iterative implementations of all three algorithms; heap sort is connected through a list adapter.
- For both array-based heap sort implementations, returning the input unchanged is equivalent to the input already being ascending. This is a necessary and sufficient condition for arbitrary lengths, including inputs with duplicates.
- The array-level heap sort specification also characterizes output equality exactly: two outputs agree if and only if the input arrays' lists are permutations. This applies to two loop-based runs, two recursive runs, and runs that use different implementations, for arbitrary input arrays.
- Filtering by any Boolean predicate commutes with both heap sort and quick sort implementations. Array heap sort is connected to the shared list specification, and `Correct.sort_filter` derives each result.
- The same `Correct.sort_filter` theorem applies to recursive and iterative merge sort, so this law follows from sorting correctness independently of the loop strategy.
- For any sorter satisfying `Correct`, sorting a concatenated input equals merging the separately sorted parts. This general law is applied to recursive and iterative merge sort and quick sort, as well as array-based heap sort.
- For any sorter satisfying the shared `Correct` specification, sorting a concatenation of chunks equals sorting each chunk with that same sorter and merging the results from right to left. This general theorem is applied independently to recursive and iterative merge sort.
- The same specification shows that permuting the chunk list leaves both the sorted concatenation and the right-folded merge result unchanged. This holds for any chunk permutation and does not depend on an implementation's internal merge schedule.
- For any binary merge tree with ascending leaf runs, if its concatenated leaves are a permutation of a given run list, its evaluation equals that run list's right-folded merge. This proves result independence from the shape of the merge tree.
- Any ascending-run merge tree also equals the output of any `Correct` sorter on the same input or a permutation-equivalent input, directly connecting arbitrary merge schedules to independent sorting implementations.
- For either heap sort implementation, sorting a concatenated array equals sorting each half separately and merging the two results with merge sort's `merge`, for arbitrary inputs. This decomposition and recomposition law follows from each stage's correctness and uniqueness of the shared specification.
- Both recursive and loop-based heap sort outputs equal the result array of the independent merge sort for every input. Uniqueness of outputs satisfying the shared sorting specification makes this a general direct comparison with another implementation.
- Every output position of recursive and iterative merge sort, quick sort, and heap sort is characterized by the input counts below and at most its value. This gives the exact rank interval of each output value, including duplicates in arbitrary inputs.
- For both recursive and loop-based heap sort, the prefix count laws are exposed directly for `<`, `≤`, `>`, and `≥` thresholds, for arbitrary lengths and threshold values. These array-level theorems connect the shared top-k specification to each implementation.
- Recursive and iterative merge sort and quick sort now also expose the `≤`, `>`, and `≥` prefix count laws directly. Together with their existing `<` laws, every sorting implementation has the full set of top-k count guarantees.
- For any threshold, the first `k` output elements contain exactly `min(k, input count below the threshold)` values below it. This characterizes the prefix as selecting the smallest side of the input, including duplicate values.
- For any sorter result satisfying the shared `Correct` specification, the first `k` elements contain exactly `min(k, input count at most the threshold)` values at most the threshold. This characterizes the boundary count including duplicates equal to the threshold.
- The same prefix contains exactly the smaller of the input count above the threshold and the `k` slots left after counting values at most the threshold. Together, the two laws characterize both sides of the boundary, including duplicates.
- The corresponding count for values greater than or equal to the threshold also holds over all naturals, including the zero-threshold boundary.
- After dropping the first `k` elements, the suffix count at most the threshold equals the input count minus the count consumed by the prefix. Multiplicities remain exact across the `take`/`drop` split.
- The suffix count above the threshold is likewise the input count minus the amount selected by the prefix, giving exact general formulas for both sides of the boundary.
- The suffix count greater than or equal to the threshold follows the same law, including the zero-threshold case. Prefix and suffix counts now cover `<`, `≤`, `>`, and `≥` predicates.
- For any Boolean predicate, the suffix count also equals the total input count minus the prefix count. This partition law follows from element preservation and does not depend on sort order.
- The additive form is also proved directly: prefix count plus suffix count equals the total input count. It states the partition without relying on natural-number subtraction.
- The output is strictly ascending exactly when the input contains no duplicates. Thus duplicate-freedom can be characterized from the sorted values for arbitrary inputs.
- For nonempty inputs, the first output of each implementation is an input minimum and the last output is an input maximum. The general theorems also prove membership and bounds against every input value.
- Uniqueness of the shared `Correct` specification proves for both implementations that the output depends only on the input multiset, not its order, and that sorting an output again leaves it unchanged.

### Finite checks

- Both heap builders are checked for the heap invariant and element preservation on 121 basic inputs, all 87,381 arrays of length 0–8 over values 0–3, all 97,656 arrays of length 0–7 over 64-bit boundary values, and 48 boundary patterns at lengths 63–513.
- Both `siftDown` implementations are checked for output agreement and element preservation at each root position over these domains. The residual contract is also checked for all four combinations of the two builders and the two `popMax` implementations.
- Both sorting implementations are checked for specification compliance and agreement on representative length-64 and length-63–513 boundary inputs, 64-bit boundary-value inputs, and sorted, reverse, all-equal, and periodic patterns at lengths 1,023–1,025.

### Remaining work

The pure CLI input parser is verified against an independent specification for arbitrary strings. Every sorting CLI now uses the shared number-list formatter, and the pure output strings from recursive and iterative HeapSort, MergeSort, and QuickSort are proved equal to the string produced by independent MergeSort for arbitrary inputs. Standard input/output and newline writes are not formally verified. Every sorting implementation is proved `Correct` for arbitrary inputs and passes the independent Boolean checker.
