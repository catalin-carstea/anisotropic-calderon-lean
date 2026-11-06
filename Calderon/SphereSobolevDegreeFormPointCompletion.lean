import Calderon.SphereSobolevFiniteDegreePairBound
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData
import Calderon.SphereSobolevFiniteDegreeDualForm
import Calderon.SphereSobolevFinitePhysicalHalfDualPackets
import Calderon.SphereSobolevFiniteHalfDualDenseExtension
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap
/-! Full upfront EXPANSION-v001.json. Abstract actual-space point seam;
actual inverse-family graph and finite bound must be independently derived. -/
attribute [local irreducible] sphereSobolevSingleL sphereSobolevCoefficientL sphereSobolevInclusionL

lemma exists_half_degree_extension_of_decoded_form_bound
    (T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (K : ∀ m n : ℕ, harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m)
    (hCoefficients : ∀ m n : ℕ, ∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (T (sphereSobolevSingleL (3/2:ℝ) n z)) = ((m:ℝ)-(n:ℝ)) • K m n z)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ ncut : ℕ, ∀ u v : ∀ l, harmonicSphereSubspace l,
      |∑ m ∈ Finset.range ncut, ∑ n ∈ Finset.range ncut, ((m:ℝ)-(n:ℝ))*⟪K m n (u n),v m⟫_ℝ| ≤
        M*Real.sqrt (∑ l ∈ Finset.range ncut, (1+(l:ℝ))*‖u l‖^2)*Real.sqrt (∑ l ∈ Finset.range ncut, (1+(l:ℝ))*‖v l‖^2)) :
    ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)), ‖S‖ ≤ M ∧
      (∀ u, S (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) = T u) ∧
      ∀ m n : ℕ, ∀ z : harmonicSphereSubspace n,
        sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z)) = ((m:ℝ)-(n:ℝ)) • K m n z := by
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_PROOF_ENTER"; out.flush
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_I_READY"; out.flush
  have hFinite := finite_half_dual_degree_pair_bound_of_decoded_form_bound T K hCoefficients M hM hBound
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_FINITE_PAIR_READY"; out.flush
  have hGeneric := exists_half_extension_of_finite_half_dual_pairs
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_EXTENSION_GENERIC_CACHED"; out.flush
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hGeneric
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_EXTENSION_GENERIC_NORMALIZED"; out.flush
  have hExtension :
    ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ‖S‖ ≤ M ∧
      (∀ u : SphereSobolev (3/2:ℝ), S (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) = T u) ∧
      (∀ m n : ℕ, ∀ z : harmonicSphereSubspace n,
        sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z)) =
        sphereSobolevCoefficientL (-(1/2:ℝ)) m (T (sphereSobolevSingleL (3/2:ℝ) n z))) := by
    run_tac do let out ← IO.getStdout; out.putStrLn "POINT_EXTENSION_TYPED_RESULT_ENTER"; out.flush
    try simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq]
    exact hGeneric T M hM hFinite
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_EXTENSION_TYPED_RESULT_READY"; out.flush
  obtain ⟨S,hNorm,hGraph,hCoeffs⟩ := hExtension
  run_tac do let out ← IO.getStdout; out.putStrLn "POINT_EXTENSION_OBTAINED_BEFORE_EXACT"; out.flush
  exact ⟨S,hNorm,hGraph,fun m n z => (hCoeffs m n z).trans (hCoefficients m n z)⟩
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.exists_half_degree_extension_of_decoded_form_bound
end OAI.AnisotropicCalderon.SphereHarmonic
