OBJS = transenv.cmo yulast.cmo sckspec.cmo ts.cmo parser.cmo scanner.cmo yults.cmo

yults : $(OBJS)
	ocamlc str.cma -o yults $(OBJS)

scanner.ml : scanner.mll
	ocamllex scanner.mll

parser.ml parser.mli : parser.mly
	ocamlyacc parser.mly

%.cmo : %.ml
	ocamlc str.cma -c $<

%.cmi : %.mli
	ocamlc str.cma -c $<

.PHONY : clean
clean :
	rm -f yults parser.ml parser.mli scanner.ml *.cmo *.cmi


sckspec.cmo :
sckspec.cmx :
yulast.cmo :
yulast.cmx :
transenv.cmo : sckspec.cmo yulast.cmo
transenv.cmx : sckspec.cmx yulast.cmx

ts.cmo : transenv.cmo sckspec.cmo yulast.cmo
ts.cmx : transenv.cmx sckspec.cmx yulast.cmx
parser.cmo : yulast.cmo parser.cmi
parser.cmx : yulast.cmx parser.cmi
parser.cmi : yulast.cmo
scanner.cmo : parser.cmi
scanner.cmx : parser.cmx
yults.cmo : scanner.cmo parser.cmi ts.cmo
yults.cmx : scanner.cmx parser.cmx ts.cmx
