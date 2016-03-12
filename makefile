all: partial.vo namesAndTypes.vo syntax.vo classTable.vo heap.vo sframe.vo reductions.vo typing.vo

%.vo: %.v
	coqc $^
