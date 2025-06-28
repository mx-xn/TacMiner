plugin/bignums_syntax_plugin_MLPACK_DEPENDENCIES:=plugin/bignums_syntax
plugin/bignums_syntax.cmx : FOR_PACK=-for-pack Bignums_syntax_plugin
plugin/bignums_syntax_plugin.cmo:$(addsuffix .cmo,$(plugin/bignums_syntax_plugin_MLPACK_DEPENDENCIES))
plugin/bignums_syntax_plugin.cmx:$(addsuffix .cmx,$(plugin/bignums_syntax_plugin_MLPACK_DEPENDENCIES))
