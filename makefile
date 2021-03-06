all: partial.vo namesAndTypes.vo syntax.vo classTable.vo heap.vo sframe.vo reductions.vo typing.vo wf_env.vo preservation.vo fs_preservation.vo ocap.vo progress_sf.vo progress.vo

%.vo : %.v
	coqc $<



## coqdep ./ *v >> makefile

classTable.vo classTable.glob classTable.v.beautified: classTable.v syntax.vo partial.vo namesAndTypes.vo
classTable.vio: classTable.v syntax.vio partial.vio namesAndTypes.vio
fs_preservation.vo fs_preservation.glob fs_preservation.v.beautified: fs_preservation.v syntax.vo partial.vo heap.vo classTable.vo sframe.vo reductions.vo typing.vo namesAndTypes.vo preservation.vo wf_env.vo
fs_preservation.vio: fs_preservation.v syntax.vio partial.vio heap.vio classTable.vio sframe.vio reductions.vio typing.vio namesAndTypes.vio preservation.vio wf_env.vio
globals.vo globals.glob globals.v.beautified: globals.v syntax.vo partial.vo namesAndTypes.vo heap.vo classTable.vo wf_env.vo
globals.vio: globals.v syntax.vio partial.vio namesAndTypes.vio heap.vio classTable.vio wf_env.vio
heap.vo heap.glob heap.v.beautified: heap.v syntax.vo namesAndTypes.vo classTable.vo
heap.vio: heap.v syntax.vio namesAndTypes.vio classTable.vio
namesAndTypes.vo namesAndTypes.glob namesAndTypes.v.beautified: namesAndTypes.v partial.vo
namesAndTypes.vio: namesAndTypes.v partial.vio
ocap.vo ocap.glob ocap.v.beautified: ocap.v syntax.vo partial.vo namesAndTypes.vo classTable.vo
ocap.vio: ocap.v syntax.vio partial.vio namesAndTypes.vio classTable.vio
partial.vo partial.glob partial.v.beautified: partial.v
partial.vio: partial.v
preservation.vo preservation.glob preservation.v.beautified: preservation.v syntax.vo partial.vo heap.vo classTable.vo sframe.vo reductions.vo typing.vo namesAndTypes.vo wf_env.vo
preservation.vio: preservation.v syntax.vio partial.vio heap.vio classTable.vio sframe.vio reductions.vio typing.vio namesAndTypes.vio wf_env.vio
progress.vo progress.glob progress.v.beautified: progress.v syntax.vo partial.vo heap.vo classTable.vo sframe.vo reductions.vo typing.vo namesAndTypes.vo wf_env.vo
progress.vio: progress.v syntax.vio partial.vio heap.vio classTable.vio sframe.vio reductions.vio typing.vio namesAndTypes.vio wf_env.vio
progress_sf.vo progress_sf.glob progress_sf.v.beautified: progress_sf.v syntax.vo partial.vo heap.vo classTable.vo sframe.vo reductions.vo typing.vo namesAndTypes.vo wf_env.vo
progress_sf.vio: progress_sf.v syntax.vio partial.vio heap.vio classTable.vio sframe.vio reductions.vio typing.vio namesAndTypes.vio wf_env.vio
reductions.vo reductions.glob reductions.v.beautified: reductions.v syntax.vo partial.vo heap.vo classTable.vo sframe.vo namesAndTypes.vo ocap.vo
reductions.vio: reductions.v syntax.vio partial.vio heap.vio classTable.vio sframe.vio namesAndTypes.vio ocap.vio
sframe.vo sframe.glob sframe.v.beautified: sframe.v syntax.vo partial.vo heap.vo classTable.vo namesAndTypes.vo
sframe.vio: sframe.v syntax.vio partial.vio heap.vio classTable.vio namesAndTypes.vio
syntax.vo syntax.glob syntax.v.beautified: syntax.v partial.vo namesAndTypes.vo
syntax.vio: syntax.v partial.vio namesAndTypes.vio
typing.vo typing.glob typing.v.beautified: typing.v syntax.vo partial.vo heap.vo classTable.vo sframe.vo reductions.vo namesAndTypes.vo ocap.vo
typing.vio: typing.v syntax.vio partial.vio heap.vio classTable.vio sframe.vio reductions.vio namesAndTypes.vio ocap.vio
wf_env.vo wf_env.glob wf_env.v.beautified: wf_env.v syntax.vo partial.vo heap.vo classTable.vo sframe.vo reductions.vo typing.vo namesAndTypes.vo
wf_env.vio: wf_env.v syntax.vio partial.vio heap.vio classTable.vio sframe.vio reductions.vio typing.vio namesAndTypes.vio
