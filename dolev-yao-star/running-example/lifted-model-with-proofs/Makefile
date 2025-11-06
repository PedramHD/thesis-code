include ../../Makefile

APP_FST_FILES=Protocol.fst Debug.fst
APP_CMX_FILES=ocaml-symbolic/Protocol.cmx ocaml-symbolic/Debug.cmx

ALL_FST_FILES=$(LIB_BASE_FST_FILES) $(LIB_FST_FILES) $(APP_FST_FILES)
ALL_CMX_FILES=$(LIB_BASE_CMX_FILES) $(LIB_CMX_FILES) $(APP_CMX_FILES)

extract: $(ALL_FST_FILES) $(ALL_CMX_FILES)
test: $(ALL_FST_FILES) $(ALL_CMX_FILES) ocaml-symbolic/test.exe

ocaml-symbolic/test.exe: $(ALL_CMX_FILES)
	$(OCAMLOPT) $^ -o $@
