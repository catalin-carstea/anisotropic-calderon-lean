import Calderon.LiteratureHarmonicDecomposition
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Open collaborator task. Read 02-density.md before changing the proof. -/
noncomputable section
open MeasureTheory MvPolynomial
namespace OAI.AnisotropicCalderon.SphereHarmonic

/-- The `i`-th coordinate function on the unit sphere. -/
def coordSphere (i : Fin 3) : C(UnitSphere, ℝ) := ⟨fun x => (x.val : Fin 3 → ℝ) i, by fun_prop⟩

lemma polynomialSphere_eq_aeval (p : MvPolynomial (Fin 3) ℝ) :
    polynomialSphere p = aeval coordSphere p := by
  ext x
  induction p using MvPolynomial.induction_on with
  | C a => simp [polynomialSphere]
  | add p q hp hq => simp_all [polynomialSphere]
  | mul_X p i hp => simp_all [polynomialSphere, coordSphere]

lemma polynomialSphere_denseRange : DenseRange polynomialSphere := by
  let A : Subalgebra ℝ C(UnitSphere, ℝ) := (aeval coordSphere).range
  have hA : A.topologicalClosure = ⊤ := by
    apply ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    intro x y hxy
    have : (x.val : Fin 3 → ℝ) ≠ (y.val : Fin 3 → ℝ) := by
      intro h; apply hxy; ext1; exact WithLp.ofLp_injective _ h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp this
    exact ⟨_, ⟨coordSphere i, ⟨X i, by simp⟩, rfl⟩, by simpa [coordSphere] using hi⟩
  have hr : Set.range polynomialSphere = (A : Set C(UnitSphere, ℝ)) := by
    ext f; simp [A, polynomialSphere_eq_aeval]
  rw [DenseRange, hr, dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, hA]
  rfl

lemma polynomialSphereL2_denseRange : DenseRange polynomialSphereL2 := by
  have h := ContinuousMap.toLp_denseRange ℝ sphereProbability ℝ (p := 2) (by simp)
  exact h.comp polynomialSphere_denseRange (ContinuousMap.toLp 2 sphereProbability ℝ).continuous

lemma eval_normSqPoly_sphere (x : UnitSphere) :
    normSqPoly.eval (x.val : Fin 3 → ℝ) = 1 := by
  have h1 : ‖x.val‖ = 1 := by simp
  have h2 := EuclideanSpace.norm_sq_eq x.val
  simp only [h1, one_pow, Real.norm_eq_abs, sq_abs] at h2
  simp [normSqPoly, h2]

lemma polynomialSphereL2_normSqPoly_pow_mul (j : ℕ) (h : MvPolynomial (Fin 3) ℝ) :
    polynomialSphereL2 (normSqPoly ^ j * h) = polynomialSphereL2 h := by
  have : polynomialSphere (normSqPoly ^ j * h) = polynomialSphere h := by
    ext x; simp [polynomialSphere, eval_normSqPoly_sphere x]
  change ContinuousMap.toLp 2 sphereProbability ℝ (polynomialSphere _) =
    ContinuousMap.toLp 2 sphereProbability ℝ (polynomialSphere _)
  rw [this]

lemma polynomialSphereL2_mem_iSup (p : MvPolynomial (Fin 3) ℝ) :
    polynomialSphereL2 p ∈ ⨆ k : ℕ, harmonicSphereSubspace k := by
  have hdec : ∀ k, harmonicDecompSpan k ≤
      (⨆ k : ℕ, harmonicSphereSubspace k).comap polynomialSphereL2 := by
    intro k
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, m, -, h, hh, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, polynomialSphereL2_normSqPoly_pow_mul]
    exact Submodule.mem_iSup_of_mem m ⟨h, hh, rfl⟩
  rw [← sum_homogeneousComponent p, map_sum]
  exact Submodule.sum_mem _ fun d _ =>
    hdec d (homogeneous_mem_harmonicDecompSpan (homogeneousComponent_isHomogeneous d p))

/-- Prove the exact interface without extra hypotheses. -/
theorem denseSphereHarmonics : DenseSphereHarmonics := by
  rw [DenseSphereHarmonics, ← Submodule.dense_iff_topologicalClosure_eq_top]
  refine polynomialSphereL2_denseRange.mono ?_
  rintro _ ⟨p, rfl⟩
  exact polynomialSphereL2_mem_iSup p

end OAI.AnisotropicCalderon.SphereHarmonic
