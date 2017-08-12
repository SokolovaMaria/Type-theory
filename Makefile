1 = HW1
R = HW1_reduction
U = HW2_unify
I = HW2_inference
T = tests

all: compile_hw1 test_reduction test_unify test_inference

compile_hw1: 
		ocamlc -I $(1)/ -c $(1)/hw1.mli $(1)/hw1.ml

test_reduction :
		ocamlc -I $(1)/ -I $(R)/  $(1)/hw1.cmo \
		$(R)/hw1_reduction.mli $(R)/hw1_reduction.ml \
		$(T)/reduction_test.ml -o reduction_test

test_unify :
		ocamlc -I $(1)/ -I $(U)/ \
		$(U)/hw2_unify.mli $(U)/hw2_unify.ml \
		$(T)/unify_test.ml -o unify_test 

test_inference:
		ocamlc -I $(1)/ -I $(R)/ -I $(U)/ -I $(I)/ \
		$(1)/hw1.cmo $(R)/hw1_reduction.cmo $(U)/hw2_unify.cmo \
		$(I)/hw2_inference.mli $(I)/hw2_inference.ml \
		$(T)/inference_test.ml -o inference_test 

clean: 		
		rm -f $(1)/*.cmi $(1)/*.cmo \
		$(R)/*.cmi $(R)/*.cmo \
		$(U)/*.cmi $(U)/*.cmo \
		$(I)/*.cmi $(I)/*.cmo \
		$(T)/*.cmi $(T)/*.cmo