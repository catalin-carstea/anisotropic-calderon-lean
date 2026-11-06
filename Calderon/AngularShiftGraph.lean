import Calderon.HarmonicDerivativeBounds
import Calderon.SpectralWeightedGraph
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.AngularShiftGraph
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SpectralWeightedGraph HarmonicDerivativeOperator

attribute [local irreducible] harmonicDerivative harmonicDerivativeAdjoint
  sphereHarmonicDecomposition

/-- The maximal actual harmonic-extension derivative, including its constant output. -/
def sphereDerivativeGraph (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) : Submodule ℝ (SphereL2 × SphereL2) where
  carrier := {z | ∀ m, sphereHarmonicCoordinate hO hD m z.2 =
    harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) z.1)}
  zero_mem' := by intro m; simp
  add_mem' := by
    intro z z' hz hz' m
    simp only [Prod.fst_add,Prod.snd_add,map_add]
    rw [hz m,hz' m]
  smul_mem' := by
    intro c z hz m
    change sphereHarmonicCoordinate hO hD m (c • z.2) =
      harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) (c • z.1))
    rw [map_smul,map_smul,map_smul,hz m]

/-- The maximal actual sphere adjoint. The constant input is retained. -/
def sphereRaisingGraph (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) : Submodule ℝ (SphereL2 × SphereL2) where
  carrier := {z | sphereHarmonicCoordinate hO hD 0 z.2 = 0 ∧ ∀ m,
    sphereHarmonicCoordinate hO hD (m+1) z.2 =
      harmonicDerivativeAdjoint hF m i (sphereHarmonicCoordinate hO hD m z.1)}
  zero_mem' := by simp
  add_mem' := by
    intro z z' hz hz'
    constructor
    · simp only [Prod.snd_add,map_add,hz.1,hz'.1,add_zero]
    · intro m
      simp only [Prod.fst_add,Prod.snd_add,map_add]
      rw [hz.2 m,hz'.2 m]
  smul_mem' := by
    intro c z hz
    constructor
    · change sphereHarmonicCoordinate hO hD 0 (c • z.2) = 0
      rw [map_smul,hz.1,smul_zero]
    · intro m
      change sphereHarmonicCoordinate hO hD (m+1) (c • z.2) =
        harmonicDerivativeAdjoint hF m i (sphereHarmonicCoordinate hO hD m (c • z.1))
      rw [map_smul,map_smul,map_smul,hz.2 m]

lemma sphereDerivativeGraph_output_unique (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u v v' : SphereL2) (hv : (u,v) ∈ sphereDerivativeGraph hF hO hD i)
    (hv' : (u,v') ∈ sphereDerivativeGraph hF hO hD i) : v = v' := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext m
  exact (hv m).trans (hv' m).symm

lemma sphereRaisingGraph_output_unique (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u v v' : SphereL2) (hv : (u,v) ∈ sphereRaisingGraph hF hO hD i)
    (hv' : (u,v') ∈ sphereRaisingGraph hF hO hD i) : v = v' := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext m
  cases m with
  | zero => exact hv.1.trans hv'.1.symm
  | succ m => exact (hv.2 m).trans (hv'.2 m).symm

lemma isClosed_sphereDerivativeGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3) :
    IsClosed (sphereDerivativeGraph hF hO hD i : Set (SphereL2 × SphereL2)) := by
  change IsClosed {z : SphereL2 × SphereL2 | ∀ m,
    sphereHarmonicCoordinate hO hD m z.2 =
      harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) z.1)}
  simp_rw [ofPred_forall]
  apply isClosed_iInter
  intro m
  exact isClosed_eq ((sphereHarmonicCoordinate hO hD m).continuous.comp continuous_snd)
    ((harmonicDerivative hF m i).continuous.comp
      ((sphereHarmonicCoordinate hO hD (m+1)).continuous.comp continuous_fst))

lemma isClosed_sphereRaisingGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3) :
    IsClosed (sphereRaisingGraph hF hO hD i : Set (SphereL2 × SphereL2)) := by
  change IsClosed {z : SphereL2 × SphereL2 | sphereHarmonicCoordinate hO hD 0 z.2 = 0 ∧
    ∀ m, sphereHarmonicCoordinate hO hD (m+1) z.2 =
      harmonicDerivativeAdjoint hF m i (sphereHarmonicCoordinate hO hD m z.1)}
  rw [setOf_and]
  apply IsClosed.inter
  · exact isClosed_eq ((sphereHarmonicCoordinate hO hD 0).continuous.comp continuous_snd)
      continuous_const
  · simp_rw [ofPred_forall]
    apply isClosed_iInter
    intro m
    exact isClosed_eq ((sphereHarmonicCoordinate hO hD (m+1)).continuous.comp continuous_snd)
      ((harmonicDerivativeAdjoint hF m i).continuous.comp
        ((sphereHarmonicCoordinate hO hD m).continuous.comp continuous_fst))

def derivativeCoordinateSequence (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) (u : SphereL2) :
    (m : ℕ) → harmonicSphereSubspace m :=
  fun m => harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) u)

def raisingCoordinateSequence (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) (u : SphereL2) :
    (m : ℕ) → harmonicSphereSubspace m
  | 0 => 0
  | m+1 => harmonicDerivativeAdjoint hF m i (sphereHarmonicCoordinate hO hD m u)

lemma exists_sphereDerivativeGraph_iff_summable (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3) (u : SphereL2) :
    (∃ v : SphereL2, (u,v) ∈ sphereDerivativeGraph hF hO hD i) ↔
      Summable (fun m : ℕ =>
        ‖harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) u)‖^2) := by
  constructor
  · rintro ⟨v,hv⟩
    change ∀ m, sphereHarmonicCoordinate hO hD m v =
      harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) u) at hv
    have hs := (lp.memℓp (sphereHarmonicDecomposition hO hD v)).summable
      (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,← sphereHarmonicCoordinate_apply,hv] using hs
  · intro hs
    have hp : Memℓp (derivativeCoordinateSequence hF hO hD i u) 2 := by
      apply (memℓp_gen_iff (show 0 < (2 : ℝ≥0∞).toReal by norm_num)).mpr
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two,derivativeCoordinateSequence] using hs
    let q : lp (fun m : ℕ => harmonicSphereSubspace m) 2 :=
      ⟨derivativeCoordinateSequence hF hO hD i u,hp⟩
    refine ⟨(sphereHarmonicDecomposition hO hD).symm q,?_⟩
    intro m
    rw [sphereHarmonicCoordinate_apply,LinearIsometryEquiv.apply_symm_apply]
    rfl

lemma exists_sphereRaisingGraph_iff_summable (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3) (u : SphereL2) :
    (∃ v : SphereL2, (u,v) ∈ sphereRaisingGraph hF hO hD i) ↔
      Summable (fun m : ℕ =>
        ‖harmonicDerivativeAdjoint hF m i (sphereHarmonicCoordinate hO hD m u)‖^2) := by
  constructor
  · rintro ⟨v,hv⟩
    have hs := (lp.memℓp (sphereHarmonicDecomposition hO hD v)).summable
      (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
    have ht := (summable_nat_add_iff 1).mpr hs
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,← sphereHarmonicCoordinate_apply,hv.2] using ht
  · intro hs
    have ht : Summable (fun m : ℕ => ‖raisingCoordinateSequence hF hO hD i u m‖^2) := by
      apply (summable_nat_add_iff 1).mp
      simpa only [raisingCoordinateSequence] using hs
    have hp : Memℓp (raisingCoordinateSequence hF hO hD i u) 2 := by
      apply (memℓp_gen_iff (show 0 < (2 : ℝ≥0∞).toReal by norm_num)).mpr
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using ht
    let q : lp (fun m : ℕ => harmonicSphereSubspace m) 2 :=
      ⟨raisingCoordinateSequence hF hO hD i u,hp⟩
    refine ⟨(sphereHarmonicDecomposition hO hD).symm q,?_,?_⟩
    · rw [sphereHarmonicCoordinate_apply,LinearIsometryEquiv.apply_symm_apply]
      rfl
    · intro m
      rw [sphereHarmonicCoordinate_apply,LinearIsometryEquiv.apply_symm_apply]
      rfl

lemma sphereDerivativeGraph_partialSum (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u v : SphereL2) (hv : (u,v) ∈ sphereDerivativeGraph hF hO hD i) (n : ℕ) :
    (sphereHarmonicPartialSum hO hD (n+1) u,sphereHarmonicPartialSum hO hD n v) ∈
      sphereDerivativeGraph hF hO hD i := by
  intro m
  simp_rw [sphereHarmonicCoordinate_partialSum]
  by_cases hm : m < n
  · simpa only [if_pos hm,if_pos (show m+1 < n+1 by omega)] using hv m
  · simp only [if_neg hm,if_neg (show ¬ m+1 < n+1 by omega),map_zero]

lemma sphereRaisingGraph_partialSum (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u v : SphereL2) (hv : (u,v) ∈ sphereRaisingGraph hF hO hD i) (n : ℕ) :
    (sphereHarmonicPartialSum hO hD n u,sphereHarmonicPartialSum hO hD (n+1) v) ∈
      sphereRaisingGraph hF hO hD i := by
  constructor
  · simpa only [sphereHarmonicCoordinate_partialSum,
      if_pos (show 0 < n+1 by omega)] using hv.1
  · intro m
    simp_rw [sphereHarmonicCoordinate_partialSum]
    by_cases hm : m < n
    · simpa only [if_pos hm,if_pos (show m+1 < n+1 by omega)] using hv.2 m
    · simp only [if_neg hm,if_neg (show ¬ m+1 < n+1 by omega),map_zero]

/-- The same finite harmonic support condition is used for both genuine operators. -/
def finiteHarmonicPair (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    Set (SphereL2 × SphereL2) :=
  {z | ∃ n : ℕ, ∀ k : ℕ, n ≤ k →
    sphereHarmonicCoordinate hO hD k z.1 = 0 ∧ sphereHarmonicCoordinate hO hD k z.2 = 0}

lemma finiteHarmonicPair_partialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u v : SphereL2) (n n' : ℕ) :
    (sphereHarmonicPartialSum hO hD n u,sphereHarmonicPartialSum hO hD n' v) ∈
      finiteHarmonicPair hO hD := by
  refine ⟨max n n',?_⟩
  intro k hk
  simp only [sphereHarmonicCoordinate_partialSum,
    if_neg (show ¬ k < n by omega),if_neg (show ¬ k < n' by omega),and_self]

lemma closure_finite_sphereDerivativeGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3) :
    closure ((sphereDerivativeGraph hF hO hD i : Set (SphereL2 × SphereL2)) ∩
      finiteHarmonicPair hO hD) = (sphereDerivativeGraph hF hO hD i : Set (SphereL2 × SphereL2)) := by
  apply Subset.antisymm
  · exact closure_minimal (fun _ hz => hz.1) (isClosed_sphereDerivativeGraph hF hO hD i)
  · intro z hz
    have ht := ((tendsto_sphereHarmonicPartialSum hO hD z.1).comp
      (tendsto_add_atTop_nat 1)).prodMk_nhds (tendsto_sphereHarmonicPartialSum hO hD z.2)
    exact isClosed_closure.mem_of_tendsto ht (Eventually.of_forall (fun n => subset_closure
      ⟨sphereDerivativeGraph_partialSum hF hO hD i z.1 z.2 hz n,
        finiteHarmonicPair_partialSum hO hD z.1 z.2 (n+1) n⟩))

lemma closure_finite_sphereRaisingGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3) :
    closure ((sphereRaisingGraph hF hO hD i : Set (SphereL2 × SphereL2)) ∩
      finiteHarmonicPair hO hD) = (sphereRaisingGraph hF hO hD i : Set (SphereL2 × SphereL2)) := by
  apply Subset.antisymm
  · exact closure_minimal (fun _ hz => hz.1) (isClosed_sphereRaisingGraph hF hO hD i)
  · intro z hz
    have ht := (tendsto_sphereHarmonicPartialSum hO hD z.1).prodMk_nhds
      ((tendsto_sphereHarmonicPartialSum hO hD z.2).comp (tendsto_add_atTop_nat 1))
    exact isClosed_closure.mem_of_tendsto ht (Eventually.of_forall (fun n => subset_closure
      ⟨sphereRaisingGraph_partialSum hF hO hD i z.1 z.2 hz n,
        finiteHarmonicPair_partialSum hO hD z.1 z.2 n (n+1)⟩))

/-- Adjunction on the maximal all-degree graphs, proved using genuine sphere Parseval. -/
lemma sphereDerivativeGraph_inner_adjoint (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u du v rv : SphereL2) (hdu : (u,du) ∈ sphereDerivativeGraph hF hO hD i)
    (hrv : (v,rv) ∈ sphereRaisingGraph hF hO hD i) :
    ⟪du,v⟫_ℝ = ⟪u,rv⟫_ℝ := by
  have hsum : Summable (fun m : ℕ =>
      ⟪sphereHarmonicDecomposition hO hD u m,
        sphereHarmonicDecomposition hO hD rv m⟫_ℝ) :=
    lp.summable_inner (𝕜 := ℝ) (G := fun k : ℕ => harmonicSphereSubspace k)
      (sphereHarmonicDecomposition hO hD u) (sphereHarmonicDecomposition hO hD rv)
  have hcoord : Summable (fun m : ℕ =>
      ⟪sphereHarmonicCoordinate hO hD m u,sphereHarmonicCoordinate hO hD m rv⟫_ℝ) := by
    simpa only [sphereHarmonicCoordinate_apply] using hsum
  rw [inner_sphereHarmonicDecomposition hO hD u rv]
  change ⟪du,v⟫_ℝ = ∑' m : ℕ,
    ⟪sphereHarmonicCoordinate hO hD m u,sphereHarmonicCoordinate hO hD m rv⟫_ℝ
  rw [hcoord.tsum_eq_zero_add]
  rw [hrv.1,inner_zero_right,zero_add,inner_sphereHarmonicDecomposition hO hD du v]
  apply tsum_congr
  intro m
  change ⟪sphereHarmonicCoordinate hO hD m du,sphereHarmonicCoordinate hO hD m v⟫_ℝ = _
  rw [hdu m,hrv.2 m,real_inner_comm,← inner_harmonicDerivativeAdjoint,real_inner_comm]

lemma sphereDerivativeGraph_single (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (k : ℕ) (a : harmonicSphereSubspace (k+1)) :
    ((a : SphereL2),(harmonicDerivative hF k i a : SphereL2)) ∈
      sphereDerivativeGraph hF hO hD i := by
  intro m
  simp only [sphereHarmonicCoordinate_apply,sphereHarmonicDecomposition_subtype]
  by_cases hm : m = k
  · subst m; simp
  · have hm' : m+1 ≠ k+1 := by omega
    simp [lp.single_apply,hm,hm',map_zero]

lemma sphereDerivativeGraph_constant (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (a : harmonicSphereSubspace 0) :
    ((a : SphereL2),0) ∈ sphereDerivativeGraph hF hO hD i := by
  intro m
  simp [sphereHarmonicCoordinate_apply,sphereHarmonicDecomposition_subtype,
    lp.single_apply,show m+1 ≠ 0 by omega]

lemma sphereRaisingGraph_single (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (k : ℕ) (a : harmonicSphereSubspace k) :
    ((a : SphereL2),(harmonicDerivativeAdjoint hF k i a : SphereL2)) ∈
      sphereRaisingGraph hF hO hD i := by
  constructor
  · simp [sphereHarmonicCoordinate_apply,sphereHarmonicDecomposition_subtype,
      lp.single_apply,show (0:ℕ) ≠ k+1 by omega]
  · intro m
    simp only [sphereHarmonicCoordinate_apply,sphereHarmonicDecomposition_subtype]
    by_cases hm : m = k
    · subst m; simp
    · have hm' : m+1 ≠ k+1 := by omega
      simp [lp.single_apply,hm,hm',map_zero]

lemma sphereDerivativeGraph_polynomial (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (m : ℕ) (p : harmonicHomogeneous (m+1)) :
    (polynomialSphereL2 p,polynomialSphereL2 (MvPolynomial.pderiv i p)) ∈
      sphereDerivativeGraph hF hO hD i := by
  have h := sphereDerivativeGraph_single hF hO hD i m
    (SmoothSphereRotationProjection.harmonicPolynomialSphereMap (m+1) p)
  rw [harmonicDerivative_apply_image] at h
  exact h

lemma sphereRaisingGraph_polynomial (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (m : ℕ) (p : harmonicHomogeneous m) :
    (polynomialSphereL2 p,polynomialSphereL2
      (SphereDerivativeAdjoint.sphereDerivativeAdjoint m i p)) ∈
      sphereRaisingGraph hF hO hD i := by
  have h := sphereRaisingGraph_single hF hO hD i m
    (SmoothSphereRotationProjection.harmonicPolynomialSphereMap m p)
  rw [harmonicDerivativeAdjoint_apply_image] at h
  exact h

/-- Any two genuine graph outputs can use the same finite harmonic input. -/
lemma sphereDerivativeRaisingGraph_common_partialSum (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u du ru : SphereL2) (hdu : (u,du) ∈ sphereDerivativeGraph hF hO hD i)
    (hru : (u,ru) ∈ sphereRaisingGraph hF hO hD i) (n : ℕ) :
    (sphereHarmonicPartialSum hO hD (n+1) u,sphereHarmonicPartialSum hO hD n du) ∈
        sphereDerivativeGraph hF hO hD i ∧
      (sphereHarmonicPartialSum hO hD (n+1) u,sphereHarmonicPartialSum hO hD ((n+1)+1) ru) ∈
        sphereRaisingGraph hF hO hD i :=
  ⟨sphereDerivativeGraph_partialSum hF hO hD i u du hdu n,
    sphereRaisingGraph_partialSum hF hO hD i u ru hru (n+1)⟩

/-- The maximal derivative graph is characterized by testing the actual raising graph. -/
lemma mem_sphereDerivativeGraph_iff_inner (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u du : SphereL2) :
    (u,du) ∈ sphereDerivativeGraph hF hO hD i ↔
      ∀ v rv : SphereL2, (v,rv) ∈ sphereRaisingGraph hF hO hD i →
        ⟪du,v⟫_ℝ = ⟪u,rv⟫_ℝ := by
  constructor
  · intro hdu v rv hrv
    exact sphereDerivativeGraph_inner_adjoint hF hO hD i u du v rv hdu hrv
  · intro ht m
    let q : harmonicSphereSubspace m := sphereHarmonicCoordinate hO hD m du -
      harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) u)
    have he := ht (q : SphereL2) (harmonicDerivativeAdjoint hF m i q : SphereL2)
      (sphereRaisingGraph_single hF hO hD i m q)
    rw [inner_sphereHarmonicCoordinate_right hO hD m du q,
      inner_sphereHarmonicCoordinate_right hO hD (m+1) u
        (harmonicDerivativeAdjoint hF m i q)] at he
    have hi : ⟪sphereHarmonicCoordinate hO hD (m+1) u,
        harmonicDerivativeAdjoint hF m i q⟫_ℝ =
        ⟪harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) u),q⟫_ℝ := by
      rw [real_inner_comm,inner_harmonicDerivativeAdjoint,real_inner_comm]
    rw [hi] at he
    have hq : ⟪q,q⟫_ℝ = 0 := by
      dsimp only [q]
      rw [inner_sub_left]
      exact sub_eq_zero.mpr he
    exact sub_eq_zero.mp ((inner_self_eq_zero).mp hq)

/-- The maximal raising graph is the Hilbert-adjoint graph, including degree zero. -/
lemma mem_sphereRaisingGraph_iff_inner (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u ru : SphereL2) :
    (u,ru) ∈ sphereRaisingGraph hF hO hD i ↔
      ∀ v dv : SphereL2, (v,dv) ∈ sphereDerivativeGraph hF hO hD i →
        ⟪ru,v⟫_ℝ = ⟪u,dv⟫_ℝ := by
  constructor
  · intro hru v dv hdv
    calc
      ⟪ru,v⟫_ℝ = ⟪v,ru⟫_ℝ := real_inner_comm _ _
      _ = ⟪dv,u⟫_ℝ :=
        (sphereDerivativeGraph_inner_adjoint hF hO hD i v dv u ru hdv hru).symm
      _ = ⟪u,dv⟫_ℝ := real_inner_comm _ _
  · intro ht
    constructor
    · let q : harmonicSphereSubspace 0 := sphereHarmonicCoordinate hO hD 0 ru
      have he := ht (q : SphereL2) 0 (sphereDerivativeGraph_constant hF hO hD i q)
      rw [inner_sphereHarmonicCoordinate_right hO hD 0 ru q,inner_zero_right] at he
      exact (inner_self_eq_zero).mp he
    · intro m
      let q : harmonicSphereSubspace (m+1) := sphereHarmonicCoordinate hO hD (m+1) ru -
        harmonicDerivativeAdjoint hF m i (sphereHarmonicCoordinate hO hD m u)
      have he := ht (q : SphereL2) (harmonicDerivative hF m i q : SphereL2)
        (sphereDerivativeGraph_single hF hO hD i m q)
      rw [inner_sphereHarmonicCoordinate_right hO hD (m+1) ru q,
        inner_sphereHarmonicCoordinate_right hO hD m u (harmonicDerivative hF m i q),
        ← inner_harmonicDerivativeAdjoint] at he
      have hq : ⟪q,q⟫_ℝ = 0 := by
        dsimp only [q]
        rw [inner_sub_left]
        exact sub_eq_zero.mpr he
      exact sub_eq_zero.mp ((inner_self_eq_zero).mp hq)

end OAI.AnisotropicCalderon.AngularShiftGraph
