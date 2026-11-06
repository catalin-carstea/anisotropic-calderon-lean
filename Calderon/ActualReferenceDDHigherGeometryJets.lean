import Calderon.ActualReferenceDDGeometryBounds
import Mathlib.Data.List.OfFn

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualReferenceDDHigherGeometryJets
open SmoothMetricFrame MovingFrameConnection AmbientReferenceCovariantCore
  ActualHorizontalNormBridge ActualReferenceDDGeometryBounds ActualNormalizedSphereRotation ActualReferenceParallelRaising
  SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  ReferenceDensityBounds MetricOperator ConformalDepth RadiusProfile PrincipalCommutator

abbrev BoundedCoordinateWord (N : ℕ) := Σ n : Fin (N+1), Fin n.val → Fin 3

def coordinateFieldWordPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    List (Fin 3) → (R3 → E) → R3 → E
  | [],f => f
  | k::w,f => directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w f)

def parameterCoordinateWordPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    List (Fin 3) → (ℝ × R3 → E) → ℝ × R3 → E
  | [],F => F
  | k::w,F => fun z => fderiv ℝ (parameterCoordinateWordPartial w F) z (0,coordinateDirection k)

lemma contDiff_coordinateFieldWordPartial {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (w : List (Fin 3))
    (f : R3 → E) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (coordinateFieldWordPartial w f) := by
  induction w with
  | nil => exact hf
  | cons k w ih => exact contDiff_directionalFDeriv (coordinateDirection k) _ ih

lemma contDiff_parameterCoordinateWordPartial {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (w : List (Fin 3))
    (F : ℝ × R3 → E) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (parameterCoordinateWordPartial w F) := by
  induction w with
  | nil => exact hF
  | cons k w ih =>
    exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma parameterCoordinateWordPartial_eq_slice {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (w : List (Fin 3))
    (F : ℝ × R3 → E) (hF : ContDiff ℝ ∞ F) (lam : ℝ) :
    (fun x => parameterCoordinateWordPartial w F (lam,x)) =
      coordinateFieldWordPartial w (fun x => F (lam,x)) := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    have hW := contDiff_parameterCoordinateWordPartial w F hF
    funext x
    change fderiv ℝ (parameterCoordinateWordPartial w F) (lam,x)
        (0,coordinateDirection k) =
      directionalFDeriv (coordinateDirection k)
        (coordinateFieldWordPartial w (fun y => F (lam,y))) x
    rw [← ih]
    have hp : HasFDerivAt (fun y : R3 => (lam,y))
        (ContinuousLinearMap.inr ℝ ℝ R3) x := hasFDerivAt_prodMk_right lam x
    have hd := (hW.differentiable (by simp) (lam,x)).hasFDerivAt.comp x hp
    have he := congrArg (fun T : R3 →L[ℝ] E => T (coordinateDirection k)) hd.fderiv
    simpa only [directionalFDeriv,Function.comp_def,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] using he.symm

theorem exists_parameter_coordinate_word_uniform_bound
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ι → ℝ × R3 → E) (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (K : Set R3) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ∀ i : ι, ∀ w : List (Fin 3), w.length ≤ N →
        ‖coordinateFieldWordPartial w (fun y => F i (lam,y)) x‖ ≤ M := by
  classical
  obtain ⟨M,hM,hbound⟩ := exists_uniform_bound_finite_family
    (fun t : ι × BoundedCoordinateWord N => fun z : ℝ × R3 =>
      ‖parameterCoordinateWordPartial (List.ofFn t.2.2) (F t.1) z‖)
    (fun t => (contDiff_parameterCoordinateWordPartial
      (List.ofFn t.2.2) (F t.1) (hF t.1)).continuous.norm) K hK
  refine ⟨M,hM,?_⟩
  intro lam hlam x hx i w hw
  let n : Fin (N+1) := ⟨w.length,by omega⟩
  have ht := hbound lam hlam x hx (i,⟨n,w.get⟩)
  rw [← parameterCoordinateWordPartial_eq_slice w (F i) (hF i) lam]
  simpa only [n,List.ofFn_get,abs_of_nonneg (norm_nonneg _)] using ht

theorem exists_referenceDD_fixed_geometry_uniform_coordinate_word_bounds
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (K : Set R3) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ∀ w : List (Fin 3), w.length ≤ N →
      (∀ a, ‖coordinateFieldWordPartial w
        (fun y => referenceMetricGramFrame g L (lam,y) a) x‖ ≤ M) ∧
      (∀ a j, |coordinateFieldWordPartial w
        (fun y => referenceMetricGramFrame g L (lam,y) a j) x| ≤ M) ∧
      (∀ i a, |coordinateFieldWordPartial w
        (fun y => referenceCoFrameEntry g L i a (lam,y)) x| ≤ M) ∧
      (∀ a c b, |coordinateFieldWordPartial w
        (fun y => referenceFrameConnectionCoefficient g L lam y
          (referenceMetricGramFrame g L (lam,y) a) c b) x| ≤ M) ∧
      (∀ a b j, |coordinateFieldWordPartial w
        (fun y => referenceConnectionFamily g L (lam,y)
          (referenceMetricGramFrame g L (lam,y) a)
          (referenceMetricGramFrame g L (lam,y) b) j) x| ≤ M) ∧
      (∀ a, ‖coordinateFieldWordPartial w
        (fun y => normalizedReferenceAngularConnection hO hD g L lam y
          (referenceMetricGramFrame g L (lam,y) a)) x‖ ≤ M) ∧
      (∀ a b, ‖coordinateFieldWordPartial w
        (fun y => directionalFDeriv (referenceMetricGramFrame g L (lam,y) a)
          (fun v => normalizedReferenceAngularConnection hO hD g L lam v
            (referenceMetricGramFrame g L (lam,v) b)) y) x‖ ≤ M) := by
  obtain ⟨M0,hM0,h0⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun a : Fin 3 => fun z : ℝ × R3 => referenceMetricGramFrame g L z a)
    (fun a => contDiff_referenceMetricGramFrame g hg L a) K hK N
  obtain ⟨M1,hM1,h1⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 => fun z : ℝ × R3 => referenceMetricGramFrame g L z t.1 t.2)
    (fun t => (contDiff_piLp_apply (p := 2) (i := t.2)).comp
      (contDiff_referenceMetricGramFrame g hg L t.1)) K hK N
  obtain ⟨M2,hM2,h2⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 => referenceCoFrameEntry g L t.1 t.2)
    (fun t => contDiff_referenceCoFrameEntry g hg L t.1 t.2) K hK N
  obtain ⟨M3,hM3,h3⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 × Fin 3 => fun z : ℝ × R3 =>
      referenceFrameConnectionJoint g L
        (fun q : ℝ × R3 => referenceMetricGramFrame g L q t.1) z t.2.1 t.2.2)
    (fun t => contDiff_referenceFrameConnectionJoint g hg L
      (fun q : ℝ × R3 => referenceMetricGramFrame g L q t.1)
      (contDiff_referenceMetricGramFrame g hg L t.1) t.2.1 t.2.2) K hK N
  obtain ⟨M4,hM4,h4⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 × Fin 3 => fun z : ℝ × R3 =>
      referenceConnectionFamily g L z (referenceMetricGramFrame g L z t.1)
        (referenceMetricGramFrame g L z t.2.1) t.2.2)
    (fun t => contDiff_referenceDDGammaFrameEntryJoint g hg L t.1 t.2.1 t.2.2) K hK N
  obtain ⟨M5,hM5,h5⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun a : Fin 3 => referenceDDFrameAngularConnectionJoint hO hD g L a)
    (fun a => contDiff_referenceDDFrameAngularConnectionJoint hO hD g hg L a) K hK N
  obtain ⟨M6,hM6,h6⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 => referenceDDFrameAngularConnectionDerivativeJoint hO hD g L t.1 t.2)
    (fun t => contDiff_referenceDDFrameAngularConnectionDerivativeJoint hO hD g hg L t.1 t.2) K hK N
  let M : ℝ := M0+M1+M2+M3+M4+M5+M6
  have h0M : M0 ≤ M := by dsimp [M]; linarith
  have h1M : M1 ≤ M := by dsimp [M]; linarith
  have h2M : M2 ≤ M := by dsimp [M]; linarith
  have h3M : M3 ≤ M := by dsimp [M]; linarith
  have h4M : M4 ≤ M := by dsimp [M]; linarith
  have h5M : M5 ≤ M := by dsimp [M]; linarith
  have h6M : M6 ≤ M := by dsimp [M]; linarith
  refine ⟨M,by dsimp [M]; linarith,?_⟩
  intro lam hlam x hx w hw
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro a
    exact (h0 lam hlam x hx a w hw).trans h0M
  · intro a j
    have ht := (h1 lam hlam x hx (a,j) w hw).trans h1M
    simpa only [Real.norm_eq_abs] using ht
  · intro i a
    have ht := (h2 lam hlam x hx (i,a) w hw).trans h2M
    simpa only [Real.norm_eq_abs] using ht
  · intro a c b
    have he : (fun y => referenceFrameConnectionJoint g L
        (fun q : ℝ × R3 => referenceMetricGramFrame g L q a) (lam,y) c b) =
        fun y => referenceFrameConnectionCoefficient g L lam y
          (referenceMetricGramFrame g L (lam,y) a) c b := by
      funext y
      exact referenceFrameConnectionJoint_eq g hg L
        (fun q : ℝ × R3 => referenceMetricGramFrame g L q a) (lam,y) c b
    have ht := (h3 lam hlam x hx (a,c,b) w hw).trans h3M
    rw [he] at ht
    simpa only [Real.norm_eq_abs] using ht
  · intro a b j
    have ht := (h4 lam hlam x hx (a,b,j) w hw).trans h4M
    simpa only [Real.norm_eq_abs] using ht
  · intro a
    have ht := (h5 lam hlam x hx a w hw).trans h5M
    simpa only [referenceDDFrameAngularConnectionJoint] using ht
  · intro a b
    have he : (fun y => referenceDDFrameAngularConnectionDerivativeJoint hO hD g L a b (lam,y)) =
        fun y => directionalFDeriv (referenceMetricGramFrame g L (lam,y) a)
          (fun v => normalizedReferenceAngularConnection hO hD g L lam v
            (referenceMetricGramFrame g L (lam,v) b)) y := by
      funext y
      exact referenceDDFrameAngularConnectionDerivativeJoint_eq hO hD g hg L lam y a b
    have ht := (h6 lam hlam x hx (a,b) w hw).trans h6M
    rw [he] at ht
    exact ht

end OAI.AnisotropicCalderon.ActualReferenceDDHigherGeometryJets
