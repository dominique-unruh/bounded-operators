section \<open>Collection of important results\<close>

theory Collection
  imports
    Bounded_Operators_Code

begin

subsection "bounded_csemilinear"

thm bounded_csemilinear_compose1

thm bounded_csemilinear_compose2

thm bounded_csemilinear_compose3


subsection "sesquilinear_linear"

thm bounded_sesquilinear.comp

thm bounded_sesquilinear.comp1

thm bounded_sesquilinear.comp2

thm bounded_sesquilinear_diff

subsection "cbilinear"

thm bilinear_Kronecker_delta

subsection "closure"

thm closed_scaleC

thm closure_scaleC

subsection "subspace"

thm subspace_cl

thm subspace_plus

thm subspace_INF

thm subspace_image

subsection "span"

thm span_def'

thm complex_real_span

thm finite_span_complete


subsection "cinner"

thm norm_cauchy_schwarz

subsection "Gradient derivative"

thm cGDERIV_DERIV_compose

thm cGDERIV_inverse

subsection "norm"

thm polarization_identity_plus

thm polarization_identity_minus

thm ParallelogramLaw

thm PythagoreanId

thm Pythagorean_generalized

thm Pythagorean_generalized_scalar

thm triangIneq_ell2

subsection "orthogonal_complement"

thm subspace_orthog

thm ortho_inter_zero

subsection "min dist"

thm existence_uniqueness_min_dist

thm dist_min_ortho

subsection "projection"

thm Proj_D1

thm Proj_D2

thm Proj_I

thm Proj_isProjector

thm isProjector_algebraic

thm Proj_leq

thm Proj_times

thm projection_scalar_mult

thm move_plus


subsection "kernel and eigenspace"

thm kernel_scalar_times

thm scaleC_eigenspace


subsection "Minkowski sum"

thm is_closed_subspace_asso

subsection "lattice"

(* instantiation clinear_space :: (chilbert_space) complete_orthomodular_lattice *)


subsection "orthogonality"

thm Gram_Schmidt

thm ortho_imples_independent

thm orthogonal_complement_twice

thm ortho_leq

thm DeMorganOrtho

thm DeMorganOrthoDual

thm inner_product_projection

thm Ortho_expansion_finite

subsection "Riesz Frechet"

thm riesz_frechet_representation_cblinfun_norm

thm riesz_frechet_representation_cblinfun_norm

subsection "adjoint"

thm Adj_cblinfun_plus

thm scalar_times_adj

thm adjoint_I

thm adjoint_I'

thm adjoint_D

thm adjoint_twice


subsection "convergence"

thm oCauchy_uCauchy_iff

thm onorm_ustrong_iff

thm completeness_real_cblinfun

thm onorm_strong


subsection "cbounded_linear"

thm complex_cbounded_linear

thm cbounded_linear_sum

thm bounded_linear_continuous

thm timesOp_assoc

thm timesOp_dist1

thm timesOp_dist2

thm times_adjoint

thm timesOp_assoc_clinear_space

thm scalar_op_clinear_space_assoc

thm scalar_op_op

thm op_scalar_op

thm mult_INF1

thm mult_inf_distrib'

thm applyOpSpace_span

thm applyOpSpace_less_eq

thm applyOpSpace_eq

thm apply_left_neutral

thm inverse_cblinfun_well_defined

thm applyOpSpace_Span

thm finite_complex_span_representation_bounded

thm cblinfun_operator_finite_dim

thm cblinfun_operator_basis_existence_uniq

thm mult_INF_general (* important *)

thm mult_INF

subsection "Unitary"

thm unitary_surj

thm unitary_image

subsection "Option"

thm inj_option_inv_option

subsection "ell 2"

thm completeness_ell2

thm superposition_principle_linear_ket

thm equal_basis

subsection "classical operator"

thm classical_operator_exists_inj

thm classical_operator_adjoint

subsection "complex vec"

thm complex_vec_space.module_span_complex_span

thm Span_onb_enum_gram_schmidt0

thm times_ell2_code

thm mat_of_cblinfun_ell2_to_l2bounded

(* thm mk_projector_SPAN *)

thm apply_cblinfun_Span

(* thm applyOpSpace_SPAN *)



subsection "unclassified"

thm complex_real_independent


end
