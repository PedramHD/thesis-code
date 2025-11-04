include ../Makefile

FSTAR_INCLUDE_DIRS = $(DY_HOME) $(DY_HOME)/symbolic $(DY_HOME)/communication_module

APP_BASE_FST_FILES=TLS13.Handshake.Messages.fst TLS13.Handshake.Sessions.fst TLS13.App.Messages.fst TLS13.App.Sessions.fst
APP_BASE_CMX_FILES=ocaml-symbolic/TLS13_Handshake_Messages.cmx ocaml-symbolic/TLS13_Handshake_Sessions.cmx ocaml-symbolic/TLS13_App_Messages.cmx ocaml-symbolic/TLS13_App_Sessions.cmx

APP_FST_FILES=TLS13.Handshake.Protocol.fst TLS13.API.fst 
APP_CMX_FILES=ocaml-symbolic/TLS13_Handshake_Protocol.cmx ocaml-symbolic/TLS13_API.cmx 

ALL_FST_FILES=$(LIB_BASE_FST_FILES) $(APP_BASE_FST_FILES) $(LIB_FST_FILES) $(APP_FST_FILES)
ALL_CMX_FILES=$(LIB_BASE_CMX_FILES) $(APP_BASE_CMX_FILES) $(LIB_CMX_FILES) $(APP_CMX_FILES)

extract: $(ALL_FST_FILES) $(ALL_CMX_FILES)
test: $(ALL_FST_FILES) $(ALL_CMX_FILES) ocaml-symbolic/test.exe

ocaml-symbolic/test.exe: $(ALL_CMX_FILES)
	$(OCAMLOPT) $^ -o $@
