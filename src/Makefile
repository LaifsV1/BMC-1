#Makefile for BMC-1

.DEFAULT_GOAL := all

TARGET = bmc-1.exe
ROOTS_CMO = AbstractSyntax.cmo
OTHERS_ML = BoundedSatSemantics.ml

all : $(TARGET)

$(TARGET) : $(ROOTS_CMO) $(OTHERS_ML)
	ocamlc $(ROOTS_CMO) $(OTHERS_ML) -o $(TARGET)

AbstractSyntax.cmo : AbstractSyntax.ml
	ocamlc -c AbstractSyntax.ml

clean :
	rm -f *.exe *.cmo *.cmi *~ *#