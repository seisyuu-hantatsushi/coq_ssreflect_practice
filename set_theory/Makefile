
TARGETS  = class_set.vo
TARGETS += class_set_theories.vo
TARGETS += logic_theories.vo
TARGETS += logic_pred_theories.vo
TARGETS += direct_product_theories.vo
TARGETS += binary_relation.vo
TARGETS += correspondence.vo
TARGETS += function.vo
TARGETS += function_theories.vo
TARGETS += function_composite_theories.vo

all: targets

binary_relation.vo : class_set.vo

correspondence.vo : binary_relation.vo

direct_product_theories.vo: class_set_theories.vo

class_set_theories.vo:  class_set.vo

class_set.vo: logic_theories.vo logic_pred_theories.vo

function.vo: class_set.vo direct_product_theories.vo correspondence.vo

function_theories.vo: function.vo

function_composite_theroies.vo: function_theories.vo function.vo

%.vo : %.v
	coqc $<

targets: ${TARGETS}

clean:
	rm -rf *.vo *.glob *~ .*.aux
