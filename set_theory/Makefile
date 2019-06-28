
TARGETS  = class_set.vo
TARGETS += class_set_theories.vo
TARGETS += logic.vo
TARGETS += logic_theories.vo
TARGETS += logic_pred_theories.vo
TARGETS += direct_product_theories.vo

direct_product_theories.vo: class_set_theories.vo

class_set_theories.vo:  class_set.vo

class_set.vo: logic.vo logic_theories.vo logic_pred_theories.vo

%.vo : %.v
	coqc $<

targets: ${TARGETS}

all: targets

clean:
	rm -rf *.vo *.glob *~ .*.aux
