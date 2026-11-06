import Calderon.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

lemma sphereSobolev_finite_bound_of_finiteSupport (s t q C : ℝ)
    (T : SphereSobolev s →L[ℝ] SphereSobolev t)
    (hcore : ∀ u ∈ sphereSobolevFiniteSupport s, ∀ S : Finset ℕ,
      (∑ k ∈ S, besselWeight q k^2*‖sphereSobolevCoefficientL t k (T u)‖^2) ≤ C^2*‖u‖^2)
    (u : SphereSobolev s) (S : Finset ℕ) :
    (∑ k ∈ S, besselWeight q k^2*‖sphereSobolevCoefficientL t k (T u)‖^2) ≤ C^2*‖u‖^2 := by
  have hc : IsClosed {v : SphereSobolev s |
      (∑ k ∈ S, besselWeight q k^2*‖sphereSobolevCoefficientL t k (T v)‖^2) ≤ C^2*‖v‖^2} := by
    apply isClosed_le
    · exact continuous_finset_sum S fun k hk => continuous_const.mul
        (((sphereSobolevCoefficientL t k).continuous.comp T.continuous).norm.pow 2)
    · exact continuous_const.mul (continuous_norm.pow 2)
  have hs := closure_minimal (s := sphereSobolevFiniteSupport s)
    (fun v hv => hcore v hv S) hc
  rw [closure_sphereSobolevFiniteSupport] at hs
  exact hs (Set.mem_univ u)

def sphereSobolevUpgradeValue (s t q C : ℝ)
    (T : SphereSobolev s →L[ℝ] SphereSobolev t)
    (hcut : ∀ u : SphereSobolev s, ∀ S : Finset ℕ,
      (∑ k ∈ S, besselWeight q k^2*‖sphereSobolevCoefficientL t k (T u)‖^2) ≤ C^2*‖u‖^2)
    (u : SphereSobolev s) : SphereSobolev q :=
  ⟨fun k => besselWeight q k • sphereSobolevCoefficientL t k (T u), by
    apply memℓp_gen' (C := C^2*‖u‖^2)
    intro S
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_smul,Real.norm_eq_abs,
      abs_of_pos (besselWeight_pos q _),mul_pow] using hcut u S⟩

lemma sphereSobolevUpgradeValue_apply (s t q C : ℝ)
    (T : SphereSobolev s →L[ℝ] SphereSobolev t)
    (hcut : ∀ u : SphereSobolev s, ∀ S : Finset ℕ,
      (∑ k ∈ S, besselWeight q k^2*‖sphereSobolevCoefficientL t k (T u)‖^2) ≤ C^2*‖u‖^2)
    (u : SphereSobolev s) (k : ℕ) :
    sphereSobolevUpgradeValue s t q C T hcut u k =
      besselWeight q k • sphereSobolevCoefficientL t k (T u) := rfl

lemma norm_sphereSobolevUpgradeValue_le (s t q C : ℝ) (hC : 0 ≤ C)
    (T : SphereSobolev s →L[ℝ] SphereSobolev t)
    (hcut : ∀ u : SphereSobolev s, ∀ S : Finset ℕ,
      (∑ k ∈ S, besselWeight q k^2*‖sphereSobolevCoefficientL t k (T u)‖^2) ≤ C^2*‖u‖^2)
    (u : SphereSobolev s) : ‖sphereSobolevUpgradeValue s t q C T hcut u‖ ≤ C*‖u‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2:ℝ≥0∞).toReal)
    (mul_nonneg hC (norm_nonneg _))
  intro S
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,sphereSobolevUpgradeValue_apply,
    norm_smul,Real.norm_eq_abs,abs_of_pos (besselWeight_pos q _),mul_pow] using hcut u S

def sphereSobolevUpgradeL (s t q C : ℝ) (hC : 0 ≤ C)
    (T : SphereSobolev s →L[ℝ] SphereSobolev t)
    (hcut : ∀ u : SphereSobolev s, ∀ S : Finset ℕ,
      (∑ k ∈ S, besselWeight q k^2*‖sphereSobolevCoefficientL t k (T u)‖^2) ≤ C^2*‖u‖^2) :
    SphereSobolev s →L[ℝ] SphereSobolev q :=
  LinearMap.mkContinuous
    { toFun := sphereSobolevUpgradeValue s t q C T hcut
      map_add' := by
        intro u v
        apply lp.ext
        funext k
        simp only [sphereSobolevUpgradeValue_apply,lp.coeFn_add,Pi.add_apply,map_add,smul_add]
      map_smul' := by
        intro c u
        apply lp.ext
        funext k
        simp only [sphereSobolevUpgradeValue_apply,lp.coeFn_smul,Pi.smul_apply,map_smul]
        exact smul_comm (besselWeight q k) c _ }
    C (norm_sphereSobolevUpgradeValue_le s t q C hC T hcut)

lemma sphereSobolevCoefficientL_upgrade (s t q C : ℝ) (hC : 0 ≤ C)
    (T : SphereSobolev s →L[ℝ] SphereSobolev t)
    (hcut : ∀ u : SphereSobolev s, ∀ S : Finset ℕ,
      (∑ k ∈ S, besselWeight q k^2*‖sphereSobolevCoefficientL t k (T u)‖^2) ≤ C^2*‖u‖^2)
    (u : SphereSobolev s) (k : ℕ) :
    sphereSobolevCoefficientL q k (sphereSobolevUpgradeL s t q C hC T hcut u) =
      sphereSobolevCoefficientL t k (T u) := by
  change besselWeight (-q) k • (besselWeight q k • sphereSobolevCoefficientL t k (T u)) = _
  rw [smul_smul]
  have hw : besselWeight (-q) k*besselWeight q k=1 := by
    unfold besselWeight
    rw [← Real.rpow_add (by positivity : 0 < 1+(k:ℝ)),neg_add_cancel,Real.rpow_zero]
  rw [hw,one_smul]

lemma sphereSobolevInclusionL_upgrade (s t q C : ℝ) (htq : t ≤ q) (hC : 0 ≤ C)
    (T : SphereSobolev s →L[ℝ] SphereSobolev t)
    (hcut : ∀ u : SphereSobolev s, ∀ S : Finset ℕ,
      (∑ k ∈ S, besselWeight q k^2*‖sphereSobolevCoefficientL t k (T u)‖^2) ≤ C^2*‖u‖^2) :
    (sphereSobolevInclusionL q t htq).comp (sphereSobolevUpgradeL s t q C hC T hcut) = T := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_ext t
  intro k
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion,
    sphereSobolevCoefficientL_upgrade]

end OAI.AnisotropicCalderon.SphereHarmonic
