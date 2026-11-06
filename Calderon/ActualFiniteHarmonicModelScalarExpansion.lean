import Calderon.ActualFiniteHarmonicModelAngularScalarProducts

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def coreScalarCombination {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (c : ι → R3 → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i)) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  ∑ i, coreScalar hO hD (c i) (hc i)*T i

def HasCoreScalarExpansionBound {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C : ℝ) : Prop :=
  ∃ (c : ι → R3 → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i)),
    A=coreScalarCombination hO hD T c hc ∧ (∑ i, |c i x|) ≤ C

lemma hasCoreScalarExpansionBound_nonneg {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C : ℝ)
    (h : HasCoreScalarExpansionBound hO hD T A x C) : 0 ≤ C := by
  obtain ⟨c,hc,he,hb⟩ := h
  exact (Finset.sum_nonneg (fun i _ => abs_nonneg (c i x))).trans hb

lemma hasCoreScalarExpansionBound_mono {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C D : ℝ)
    (h : HasCoreScalarExpansionBound hO hD T A x C) (hCD : C ≤ D) :
    HasCoreScalarExpansionBound hO hD T A x D := by
  obtain ⟨c,hc,he,hb⟩ := h
  exact ⟨c,hc,he,hb.trans hCD⟩

lemma hasCoreScalarExpansionBound_combination {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (c : ι → R3 → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i)) (x : R3) :
    HasCoreScalarExpansionBound hO hD T (coreScalarCombination hO hD T c hc) x
      (∑ i, |c i x|) := by
  exact ⟨c,hc,rfl,le_rfl⟩

lemma hasCoreScalarExpansionBound_zero {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) :
    HasCoreScalarExpansionBound hO hD T 0 x 0 := by
  have hz : coreScalar hO hD (fun _ => (0 : ℝ)) contDiff_const = 0 := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext y
    exact zero_smul ℝ (F.val y)
  refine ⟨fun _ _ => 0,fun _ => contDiff_const,?_,?_⟩
  · simp only [coreScalarCombination,hz,zero_mul,Finset.sum_const_zero]
  · simp only [abs_zero,Finset.sum_const_zero,le_refl]

lemma hasCoreScalarExpansionBound_single {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (i : ι)
    (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (x : R3) :
    HasCoreScalarExpansionBound hO hD T (coreScalar hO hD c hc*T i) x |c x| := by
  classical
  let d (j : ι) : R3 → ℝ := if j=i then c else fun _ => 0
  have hd (j : ι) : ContDiff ℝ ∞ (d j) := by
    by_cases hj : j=i
    · simpa only [d,if_pos hj] using hc
    · simpa only [d,if_neg hj] using (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (0 : ℝ)))
  have he (j : ι) : coreScalar hO hD (d j) (hd j)*T j =
      if j=i then coreScalar hO hD c hc*T i else 0 := by
    split_ifs with hj
    · subst j
      simp only [d,ite_true]
    · have hz : coreScalar hO hD (d j) (hd j) = 0 := by
        apply LinearMap.ext
        intro F
        apply Subtype.ext
        funext y
        change d j y • F.val y = 0
        simp only [d,if_neg hj,zero_smul]
      rw [hz,zero_mul]
  refine ⟨d,hd,?_,?_⟩
  · simp only [coreScalarCombination,he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  · have ha (j : ι) : |d j x| = if j=i then |c x| else 0 := by
      by_cases hj : j=i <;> simp only [d,hj,ite_true,ite_false,abs_zero]
    simp only [ha,Finset.sum_ite_eq',Finset.mem_univ,ite_true,le_refl]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
