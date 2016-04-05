all: partial.vo namesAndTypes.vo syntax.vo classTable.vo heap.vo sframe.vo reductions.vo typing.vo wf_env.vo 

%.vo : %.v
	coqc $<



## coqdep -I ./ *v >> makefile
classTable.vo classTable.glob classTable.v.beautified: classTable.v syntax.vo partial.vo namesAndTypes.vo
fs_preservation.vo fs_preservation.glob fs_preservation.v.beautified: fs_preservation.v syntax.vo partial.vo heap.vo classTable.vo sframe.vo reductions.vo typing.vo namesAndTypes.vo preservation.vo wf_env.vo
globals.vo globals.glob globals.v.beautified: globals.v syntax.vo partial.vo namesAndTypes.vo heap.vo classTable.vo wf_env.vo
heap.vo heap.glob heap.v.beautified: heap.v syntax.vo namesAndTypes.vo classTable.vo
namesAndTypes.vo namesAndTypes.glob namesAndTypes.v.beautified: namesAndTypes.v partial.vo
ocap.vo ocap.glob ocap.v.beautified: ocap.v syntax.vo partial.vo namesAndTypes.vo classTable.vo
partial.vo partial.glob partial.v.beautified: partial.v
preservation.vo preservation.glob preservation.v.beautified: preservation.v syntax.vo partial.vo heap.vo classTable.vo sframe.vo reductions.vo typing.vo namesAndTypes.vo wf_env.vo
reductions.vo reductions.glob reductions.v.beautified: reductions.v syntax.vo partial.vo heap.vo classTable.vo sframe.vo namesAndTypes.vo ocap.vo
sframe.vo sframe.glob sframe.v.beautified: sframe.v syntax.vo partial.vo heap.vo classTable.vo namesAndTypes.vo
syntax.vo syntax.glob syntax.v.beautified: syntax.v partial.vo namesAndTypes.vo
typing.vo typing.glob typing.v.beautified: typing.v syntax.vo partial.vo heap.vo classTable.vo sframe.vo reductions.vo namesAndTypes.vo ocap.vo
wf_env.vo wf_env.glob wf_env.v.beautified: wf_env.v syntax.vo partial.vo heap.vo classTable.vo sframe.vo reductions.vo typing.vo namesAndTypes.vo
