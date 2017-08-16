Theorems proved
==============

There are 2 threorems: progress and preservation. 

## Progress ##

The progress theorem is defined in `progress.v`. It is **Theorem 2** from the
published article.

There are things missing: In the progress theorem we have

`|- H : *` completely defined in `heap.v` as `Heap_ok`.

`H |- F : s` completely defined in `wf_env.v` as `WF_Frame`

`H ; a |- F ok` **not** at all defined.

Except for proving the progress of `H ; a |- F ok`, the proof is done (all the
admits are in *preservation*).


## Preservation ##

Same as above, the separation and ocap properties are not defined and not part
of the theorem statement. There are admits in the `assign` case.

The proof of single-frame preservation is finished, except for the two admitted
parts (which are the most tricky...)

It doesn't look like `preservation_unfixed.v` or anything else has preservation
for frame stacks.
