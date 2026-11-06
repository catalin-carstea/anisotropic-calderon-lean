/- Proves the generic order-2 budgets and radius 0..4 selection for the two-jet bound of the
actual canonical zero coefficient, and reduces `CanonicalZeroCoefficientJetTarget` (from
`ActualHigherSZeroCoefficientJets`) to the single named factorisation
`CanonicalZeroFactorisation` (identity (★) plus germs), which is proved in
`ActualHigherSZeroCoefficientFactorisation`. -/
import Calderon.ActualHigherSZeroCoefficientJets
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientJetBounds
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
open ActualHigherSFirstCoefficientJets ActualHigherSZeroCoefficientJets

section GenericSum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Finite-sum jet bound at a point, from germs only (no global smoothness). -/
lemma norm_iteratedFDeriv_finset_sum_le {ι : Type*} (u : Finset ι) (f : ι → E → F) (x : E)
    (hf : ∀ j, ContDiffAt ℝ ∞ (f j) x) (n : ℕ) (c : ι → ℝ)
    (hc : ∀ j ∈ u, ‖iteratedFDeriv ℝ n (f j) x‖ ≤ c j) :
    ‖iteratedFDeriv ℝ n (fun y => ∑ j ∈ u, f j y) x‖ ≤ ∑ j ∈ u, c j := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [iteratedFDeriv_zero_fun]
  | insert a s ha ih =>
    have hs : ContDiffAt ℝ ∞ (fun y => ∑ j ∈ s, f j y) x := ContDiffAt.sum fun j _ => hf j
    have he : (fun y => ∑ j ∈ insert a s, f j y) = f a + (fun y => ∑ j ∈ s, f j y) := by
      funext y
      simp only [Finset.sum_insert ha, Pi.add_apply]
    rw [he, iteratedFDeriv_add_apply ((hf a).of_le (by simp)) (hs.of_le (by simp)),
      Finset.sum_insert ha]
    exact (norm_add_le _ _).trans (add_le_add (hc a (Finset.mem_insert_self a s))
      (ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))))
end GenericSum

section HessianEntry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[instance_reducible] private def hessianCovectorNormed : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
attribute [local instance] hessianCovectorNormed
@[instance_reducible] private def hessianCovectorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
attribute [local instance] hessianCovectorSpace
@[instance_reducible] private def hessianOperatorNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
attribute [local instance] hessianOperatorNormed
@[instance_reducible] private def hessianOperatorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
attribute [local instance] hessianOperatorSpace

/-- A fixed linear functional of the Hessian has jets bounded by the radius jets two
orders higher (this is where the ACTUAL third/fourth radius derivatives enter). -/
lemma norm_iteratedFDeriv_hessian_entry_le (RR : E → ℝ) (hR : ContDiff ℝ ∞ RR)
    (Lh : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ) (x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => Lh (fderiv ℝ (fderiv ℝ RR) y)) x‖ ≤
      ‖Lh‖*‖iteratedFDeriv ℝ (n+1+1) RR x‖ := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ RR) := hR.fderiv_right (m := ∞) (by simp)
  have h2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ RR)) := h1.fderiv_right (m := ∞) (by simp)
  have h := Lh.norm_iteratedFDeriv_comp_left (x := x) (n := n) h2.contDiffAt (by simp)
  rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv] at h
  exact h

lemma contDiff_hessian_entry (RR : E → ℝ) (hR : ContDiff ℝ ∞ RR)
    (Lh : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (fun y => Lh (fderiv ℝ (fderiv ℝ RR) y)) :=
  Lh.contDiff.comp ((hR.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp))

/-- Order-2 budget of `R² · Lh(D²R)`: needs radius jets 0..4; uses `Rβ² ≤ 1`, `β ≥ 1`. -/
lemma radius_square_hessian_jets (RR : E → ℝ) (hR : ContDiff ℝ ∞ RR)
    (Lh : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ) (x : E) (J beta : ℝ) (hJ : 0 ≤ J)
    (hr : 0 ≤ RR x) (hb : 1 ≤ beta) (hsmall : RR x*beta^2 ≤ 1)
    (hRad : ∀ k : ℕ, k ≤ 4 → ‖iteratedFDeriv ℝ k RR x‖ ≤ (J*RR x)*beta^k) :
    ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun y => (RR y)^2 • Lh (fderiv ℝ (fderiv ℝ RR) y)) x‖ ≤
        (16*J^3*‖Lh‖)*RR x*beta^n := by
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hRad2 (k : ℕ) (hk : k ≤ 2) : ‖iteratedFDeriv ℝ k RR x‖ ≤ (J*RR x)*beta^k :=
    hRad k (hk.trans (by norm_num))
  have hRRC (k : ℕ) (hk : k ≤ 2) :
      ‖iteratedFDeriv ℝ k (fun y => (RR y)^2) x‖ ≤ (4*J^2*(RR x)^2)*beta^k := by
    have h := product_jets_two RR RR x hR.contDiffAt hR.contDiffAt
      (J*RR x) (J*RR x) beta (mul_nonneg hJ hr) (mul_nonneg hJ hr) hb0 hRad2 hRad2 k hk
    have he : (fun y : E => (RR y)^2) = (fun y : E => RR y • RR y) := by
      funext y
      simp only [smul_eq_mul, pow_two]
    rw [he]
    exact h.trans (le_of_eq (by ring))
  have hH (k : ℕ) (hk : k ≤ 2) :
      ‖iteratedFDeriv ℝ k (fun y => Lh (fderiv ℝ (fderiv ℝ RR) y)) x‖ ≤
        (J*RR x*beta^2*‖Lh‖)*beta^k := by
    have h := norm_iteratedFDeriv_hessian_entry_le RR hR Lh x k
    have hk4 : k+1+1 ≤ 4 := by omega
    have hr4 := hRad (k+1+1) hk4
    calc
      _ ≤ ‖Lh‖*‖iteratedFDeriv ℝ (k+1+1) RR x‖ := h
      _ ≤ ‖Lh‖*((J*RR x)*beta^(k+1+1)) := mul_le_mul_of_nonneg_left hr4 (norm_nonneg _)
      _ = _ := by ring
  have hR2 : ContDiffAt ℝ ∞ (fun y => (RR y)^2) x := hR.contDiffAt.pow 2
  have hHg : ContDiffAt ℝ ∞ (fun y => Lh (fderiv ℝ (fderiv ℝ RR) y)) x :=
    (contDiff_hessian_entry RR hR Lh).contDiffAt
  intro n hn
  have hfin := product_jets_two (fun y => (RR y)^2) (fun y => Lh (fderiv ℝ (fderiv ℝ RR) y)) x
    hR2 hHg (4*J^2*(RR x)^2) (J*RR x*beta^2*‖Lh‖) beta (by positivity) (by positivity) hb0
    hRRC hH n hn
  have hR1 : RR x ≤ 1 := by
    have : RR x ≤ RR x*beta^2 := le_mul_of_one_le_right hr (one_le_pow₀ hb)
    linarith
  have hkey : (RR x)^2*(RR x*beta^2) ≤ RR x := by
    have h1 : (RR x)^2*(RR x*beta^2) ≤ (RR x)^2 :=
      mul_le_of_le_one_right (sq_nonneg _) hsmall
    have h2 : (RR x)^2 ≤ RR x := by nlinarith
    linarith
  have hc : 0 ≤ 16*J^3*‖Lh‖*beta^n := by positivity
  calc
    _ ≤ (4*(4*J^2*(RR x)^2)*(J*RR x*beta^2*‖Lh‖))*beta^n := hfin
    _ = (16*J^3*‖Lh‖*beta^n)*((RR x)^2*(RR x*beta^2)) := by ring
    _ ≤ (16*J^3*‖Lh‖*beta^n)*RR x := mul_le_mul_of_nonneg_left hkey hc
    _ = _ := by ring
end HessianEntry

section FactoredAssembly
variable {E T V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Generic order-2 assembly of the factorised shape (★); the identity is required only
EVENTUALLY near `x`, and transported by `Filter.EventuallyEq.iteratedFDeriv`. -/
lemma factored_zero_jets {ι : Type*} [Fintype ι] (f : E → V) (RR : E → ℝ) (TP : E → T)
    (Φ0 : T → V) (s : ι → E → ℝ) (Ψ : ι → T → V) (x : E)
    (hf : f =ᶠ[𝓝 x] fun y => RR y • Φ0 (TP y) + ∑ i, s i y • Ψ i (TP y))
    (hR : ContDiffAt ℝ ∞ RR x) (hT : ContDiffAt ℝ ∞ TP x)
    (hΦ0 : ContDiffAt ℝ ∞ Φ0 (TP x)) (hs : ∀ i, ContDiffAt ℝ ∞ (s i) x)
    (hΨ : ∀ i, ContDiffAt ℝ ∞ (Ψ i) (TP x))
    (J M CT S beta : ℝ) (hJ : 0 ≤ J) (hM : 0 ≤ M) (hCT : 0 ≤ CT) (hS : 0 ≤ S)
    (hr : 0 ≤ RR x) (hb : 1 ≤ beta)
    (hRad : ∀ k : ℕ, k ≤ 2 → ‖iteratedFDeriv ℝ k RR x‖ ≤ (J*RR x)*beta^k)
    (hcap0 : ∀ k : ℕ, k ≤ 2 → ‖iteratedFDeriv ℝ k Φ0 (TP x)‖ ≤ M)
    (hcapΨ : ∀ i, ∀ k : ℕ, k ≤ 2 → ‖iteratedFDeriv ℝ k (Ψ i) (TP x)‖ ≤ M)
    (hT1 : ‖iteratedFDeriv ℝ 1 TP x‖ ≤ CT)
    (hT2 : ‖iteratedFDeriv ℝ 2 TP x‖ ≤ CT*beta)
    (hsj : ∀ i, ∀ k : ℕ, k ≤ 2 → ‖iteratedFDeriv ℝ k (s i) x‖ ≤ (S*RR x)*beta^k) :
    ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n f x‖ ≤
      ((8*J+8*S*(Fintype.card ι : ℝ))*M*(CT+1)^2)*RR x*beta^n := by
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  intro n hn
  have hEq := (hf.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
  rw [hEq]
  have hP0 := small_profile_composition_jets TP Φ0 x hT hΦ0 M CT beta hM hCT hb hcap0 hT1 hT2
  have h1 := product_jets_two RR (Φ0 ∘ TP) x hR (hΦ0.comp x hT) (J*RR x) (2*M*(CT+1)^2) beta
    (mul_nonneg hJ hr) (by positivity) hb0 hRad hP0 n hn
  have hi (i : ι) : ‖iteratedFDeriv ℝ n (fun y => s i y • Ψ i (TP y)) x‖ ≤
      (4*(S*RR x)*(2*M*(CT+1)^2))*beta^n := by
    have hPi := small_profile_composition_jets TP (Ψ i) x hT (hΨ i) M CT beta hM hCT hb
      (hcapΨ i) hT1 hT2
    exact product_jets_two (s i) (Ψ i ∘ TP) x (hs i) ((hΨ i).comp x hT) (S*RR x)
      (2*M*(CT+1)^2) beta (mul_nonneg hS hr) (by positivity) hb0 (hsj i) hPi n hn
  have gA : ContDiffAt ℝ ∞ (fun y => RR y • Φ0 (TP y)) x := hR.smul (hΦ0.comp x hT)
  have gB : ContDiffAt ℝ ∞ (fun y => ∑ i, s i y • Ψ i (TP y)) x :=
    ContDiffAt.sum fun i _ => (hs i).smul ((hΨ i).comp x hT)
  have hsplit : (fun y => RR y • Φ0 (TP y) + ∑ i, s i y • Ψ i (TP y)) =
      (fun y => RR y • Φ0 (TP y)) + (fun y => ∑ i, s i y • Ψ i (TP y)) := rfl
  rw [hsplit, iteratedFDeriv_add_apply (gA.of_le (by simp)) (gB.of_le (by simp))]
  have hB := norm_iteratedFDeriv_finset_sum_le (Finset.univ : Finset ι)
    (fun i y => s i y • Ψ i (TP y)) x (fun i => (hs i).smul ((hΨ i).comp x hT)) n
    (fun _ => (4*(S*RR x)*(2*M*(CT+1)^2))*beta^n) (fun i _ => hi i)
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ (4*(J*RR x)*(2*M*(CT+1)^2))*beta^n +
        ∑ _i : ι, (4*(S*RR x)*(2*M*(CT+1)^2))*beta^n := add_le_add h1 hB
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
end FactoredAssembly

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
/- Cache order: inner operator norm, then its module. -/
@[instance_reducible] private def zeroBoundsHighHalfNormed : NormedAddCommGroup (Hi →L[ℝ] Half) :=
  inferInstance
attribute [local instance] zeroBoundsHighHalfNormed
@[instance_reducible] private def zeroBoundsHighHalfSpace : NormedSpace ℝ (Hi →L[ℝ] Half) :=
  inferInstance
attribute [local instance] zeroBoundsHighHalfSpace
@[instance_reducible] private def zeroBoundsParameterNormed : NormedAddCommGroup Tpar := inferInstance
attribute [local instance] zeroBoundsParameterNormed
@[instance_reducible] private def zeroBoundsParameterModule : NormedSpace ℝ Tpar := inferInstance
attribute [local instance] zeroBoundsParameterModule


@[instance_reducible] private def nativeHessianCovectorNormed : NormedAddCommGroup (R3 →L[ℝ] ℝ) := inferInstance
attribute [local instance] nativeHessianCovectorNormed
@[instance_reducible] private def nativeHessianCovectorSpace : NormedSpace ℝ (R3 →L[ℝ] ℝ) := inferInstance
attribute [local instance] nativeHessianCovectorSpace
@[instance_reducible] private def nativeHessianOperatorNormed : NormedAddCommGroup (R3 →L[ℝ] R3 →L[ℝ] ℝ) := inferInstance
attribute [local instance] nativeHessianOperatorNormed
@[instance_reducible] private def nativeHessianOperatorSpace : NormedSpace ℝ (R3 →L[ℝ] R3 →L[ℝ] ℝ) := inferInstance
attribute [local instance] nativeHessianOperatorSpace

/-- Fixed Hessian-entry functional `A ↦ A e_m e_k` (coordinate directions). -/
def hessianEntry (mk : Fin 3 × Fin 3) : (R3 →L[ℝ] R3 →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (coordinateDirection mk.2)).comp
    (ContinuousLinearMap.apply ℝ (R3 →L[ℝ] ℝ) (coordinateDirection mk.1))

/-- Radius jets 0..4, uniform on a compact set, from the ACTUAL fixed-uniform theorem. -/
private structure RadiusFourJetData (g : MatrixField) (L : ℝ) (K : Set R3) where
  J : ℝ
  J_one : 1 ≤ J
  bounds : ∀ q ∈ Icc (0 : ℝ) 1, ∀ δr Ar : ℝ, ∀ p : ℕ,
    0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ x ∈ K,
    1 ≤ actualReferenceBeta g L q δr Ar p x →
    ∀ k : ℕ, k ≤ 4 → ‖iteratedFDeriv ℝ k (referenceRadius δr Ar p L) x‖ ≤
      (J*referenceRadius δr Ar p L x)*(actualReferenceBeta g L q δr Ar p x)^k

private theorem exists_radiusFourJetData (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    Nonempty (RadiusFourJetData g L K) := by
  obtain ⟨J1,hJ1,hR1⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 1
  obtain ⟨J2,hJ2,hR2⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 2
  obtain ⟨J3,hJ3,hR3⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 3
  obtain ⟨J4,hJ4,hR4⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 4
  let J : ℝ := 1+J1+J2+J3+J4
  have hJ : 1 ≤ J := by dsimp [J]; linarith
  refine ⟨⟨J,hJ,?_⟩⟩
  intro q hq δr Ar p hδr hδr1 hAr hp x hx hb k hk
  have hr : 0 < referenceRadius δr Ar p L x := referenceRadius_pos δr Ar p L x hδr hAr
  have hb0 : 0 ≤ actualReferenceBeta g L q δr Ar p x := zero_le_one.trans hb
  have hlift (Jk : ℝ) (hJk : Jk ≤ J) (k' : ℕ)
      (h : ‖iteratedFDeriv ℝ k' (referenceRadius δr Ar p L) x‖ ≤
        Jk*referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^k') :
      ‖iteratedFDeriv ℝ k' (referenceRadius δr Ar p L) x‖ ≤
        (J*referenceRadius δr Ar p L x)*(actualReferenceBeta g L q δr Ar p x)^k' :=
    h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hJk hr.le) (pow_nonneg hb0 k'))
  interval_cases k
  · rw [norm_iteratedFDeriv_zero,pow_zero,mul_one,Real.norm_eq_abs,abs_of_pos hr]
    exact le_mul_of_one_le_left hr.le hJ
  · exact hlift J1 (by dsimp [J]; linarith) 1
      (by simpa only [actualReferenceBeta] using (hR1 q hq δr hδr hδr1 Ar hAr p hp x hx).1)
  · exact hlift J2 (by dsimp [J]; linarith) 2
      (by simpa only [actualReferenceBeta] using (hR2 q hq δr hδr hδr1 Ar hAr p hp x hx).1)
  · exact hlift J3 (by dsimp [J]; linarith) 3
      (by simpa only [actualReferenceBeta] using (hR3 q hq δr hδr hδr1 Ar hAr p hp x hx).1)
  · exact hlift J4 (by dsimp [J]; linarith) 4
      (by simpa only [actualReferenceBeta] using (hR4 q hq δr hδr hδr1 Ar hAr p hp x hx).1)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "CZc" => canonicalZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Target" => CanonicalZeroCoefficientJetTarget
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- The exact factorisation (★) for the literal
`canonicalZeroCoefficient`, with factor germs `Φ0, Ψ` depending ONLY on the parameter
`t` (chosen after δ, g2; before δr, Ar, p, q, x).  This is an identity about the actual
objects, not a bound; no jet or compact-bound information is contained in it. -/
def CanonicalZeroFactorisation (δ : ℝ) (g2 : MatrixField) : Prop :=
  ∃ (Φ0 : Tpar → (Hi →L[ℝ] Neg)) (Ψ : Fin 3 × Fin 3 → Tpar → (Hi →L[ℝ] Neg)),
    (∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ Φ0 t) ∧
    (∀ i, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (Ψ i) t) ∧
    ∀ δr Ar : ℝ, ∀ p : ℕ, 0 < δr → 0 < Ar → ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
      (fun y => CZc g2 δr Ar p q y) =ᶠ[𝓝 x] fun y =>
        referenceRadius δr Ar p L y • Φ0 ((Tq δr Ar p q) y) +
        ∑ i, ((referenceRadius δr Ar p L y)^2 •
          hessianEntry i (fderiv ℝ (fderiv ℝ (referenceRadius δr Ar p L)) y)) •
          Ψ i ((Tq δr Ar p q) y)

/-- Reduction: `CanonicalZeroCoefficientJetTarget` follows from the named factorisation, using
ONLY native data (compact room caps, actual parameter jets, actual radius jets 0..4).
`hL` is the same native hypothesis as in the first-coefficient bound. -/
theorem canonicalZeroCoefficientJetTarget_of_factorisation
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hfac : CanonicalZeroFactorisation g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ g2) :
    Target δ g2 := by
  obtain ⟨Φ0,Ψ,hΦ0g,hΨg,hid⟩ := hfac
  have hK : IsCompact (closedBall y0 ρ) := isCompact_closedBall y0 ρ
  have hKP : IsCompact (ParamRoom δ) :=
    (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall (0 : R3 →L[ℝ] ℝ) 1)
  obtain ⟨D4⟩ := exists_radiusFourJetData g hg L hL (closedBall y0 ρ) hK
  obtain ⟨CT,hCT,hTj⟩ := exists_reference_radius_parameter_uniform_jet_bounds g hg L hL
    (closedBall y0 ρ) hK
  obtain ⟨M0,hM0,hcap0⟩ := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
    (fun (_ : Fin 1) => Φ0) (ParamRoom δ) hKP (fun _ t ht => hΦ0g t ht) 2
  obtain ⟨M1,hM1,hcap1⟩ := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
    Ψ (ParamRoom δ) hKP (fun i t ht => hΨg i t ht) 2
  let M : ℝ := 1+|M0|+|M1|
  have hM : 0 ≤ M := by positivity
  let J : ℝ := D4.J
  have hJ : 0 ≤ J := zero_le_one.trans D4.J_one
  let Lmax : ℝ := ∑ i : Fin 3 × Fin 3, ‖hessianEntry i‖
  let S : ℝ := 16*J^3*Lmax
  have hS : 0 ≤ S := by positivity
  refine ⟨1+((8*J+8*S*(Fintype.card (Fin 3 × Fin 3) : ℝ))*M*(CT+1)^2), by positivity, ?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq x hx hb hsmall n hn
  let RR : R3 → ℝ := referenceRadius δr Ar p L
  let beta : ℝ := actualReferenceBeta g L q δr Ar p x
  have hr : 0 < RR x := referenceRadius_pos δr Ar p L x hδr hAr
  have hR : ContDiff ℝ ∞ RR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hxK : x ∈ closedBall y0 ρ := by
    simpa only [ActualHigherSFormation.higherSParam] using hx.1.2.1
  have hdR : ‖fderiv ℝ RR x‖ ≤ 1 := by
    have hmem : fderiv ℝ RR x ∈ closedBall (0 : R3 →L[ℝ] ℝ) 1 := by
      simpa only [ActualHigherSFormation.higherSParam,RR] using hx.2
    exact mem_closedBall_zero_iff.mp hmem
  have ht := hTj q hq δr hδr hδr1 Ar hAr p hp x hxK hb hsmall hdR
  have he : ActualHigherSFormation.higherSParam L δr Ar p q =
      (fun z : R3 => ((q,(z,referenceRadius δr Ar p L z)),fderiv ℝ (referenceRadius δr Ar p L) z)) := by
    funext z
    unfold ActualHigherSFormation.higherSParam
    rfl
  have hParam : ContDiff ℝ ∞ (Tq δr Ar p q) := by rw [he]; exact ht.1
  have hParam1 : ‖iteratedFDeriv ℝ 1 (Tq δr Ar p q) x‖ ≤ CT := by rw [he]; exact ht.2.1
  have hParam2 : ‖iteratedFDeriv ℝ 2 (Tq δr Ar p q) x‖ ≤ CT*beta := by rw [he]; exact ht.2.2
  have hRad4 := D4.bounds q hq δr Ar p hδr hδr1 hAr hp x hxK hb
  have hRad2 (k : ℕ) (hk : k ≤ 2) : ‖iteratedFDeriv ℝ k RR x‖ ≤ (J*RR x)*beta^k :=
    hRad4 k (hk.trans (by norm_num))
  have hcapΦ (k : ℕ) (hk : k ≤ 2) : ‖iteratedFDeriv ℝ k Φ0 ((Tq δr Ar p q) x)‖ ≤ M :=
    (hcap0 k hk _ hx 0).trans ((le_abs_self M0).trans (by dsimp [M]; linarith [abs_nonneg M1]))
  have hcapΨ (i : Fin 3 × Fin 3) (k : ℕ) (hk : k ≤ 2) :
      ‖iteratedFDeriv ℝ k (Ψ i) ((Tq δr Ar p q) x)‖ ≤ M :=
    (hcap1 k hk _ hx i).trans ((le_abs_self M1).trans (by dsimp [M]; linarith [abs_nonneg M0]))
  have hLi (i : Fin 3 × Fin 3) : ‖hessianEntry i‖ ≤ Lmax :=
    Finset.single_le_sum (f := fun j => ‖hessianEntry j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ i)
  have hsj (i : Fin 3 × Fin 3) (k : ℕ) (hk : k ≤ 2) :
      ‖iteratedFDeriv ℝ k (fun y => (RR y)^2 • hessianEntry i (fderiv ℝ (fderiv ℝ RR) y)) x‖ ≤
        (S*RR x)*beta^k := by
    have h := radius_square_hessian_jets RR hR (hessianEntry i) x J beta hJ hr.le hb hsmall
      hRad4 k hk
    have hc : 0 ≤ RR x*beta^k := by positivity
    calc
      _ ≤ (16*J^3*‖hessianEntry i‖)*RR x*beta^k := h
      _ = (16*J^3*‖hessianEntry i‖)*(RR x*beta^k) := by ring
      _ ≤ S*(RR x*beta^k) := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hLi i) (by positivity)) hc
      _ = _ := by ring
  have hsg (i : Fin 3 × Fin 3) :
      ContDiffAt ℝ ∞ (fun y => (RR y)^2 • hessianEntry i (fderiv ℝ (fderiv ℝ RR) y)) x :=
    (hR.contDiffAt.pow 2).smul (contDiff_hessian_entry RR hR (hessianEntry i)).contDiffAt
  have hfin := factored_zero_jets (fun y => CZc g2 δr Ar p q y) RR (Tq δr Ar p q) Φ0
    (fun i y => (RR y)^2 • hessianEntry i (fderiv ℝ (fderiv ℝ RR) y)) Ψ x
    (hid δr Ar p hδr hAr q hq x hx) hR.contDiffAt hParam.contDiffAt (hΦ0g _ hx) hsg
    (fun i => hΨg i _ hx) J M CT S beta hJ hM hCT.le hS hr.le hb hRad2 hcapΦ hcapΨ
    hParam1 hParam2 hsj n hn
  have hc : 0 ≤ RR x*beta^n := by positivity
  calc
    _ ≤ ((8*J+8*S*(Fintype.card (Fin 3 × Fin 3) : ℝ))*M*(CT+1)^2)*RR x*beta^n := hfin
    _ ≤ (1+((8*J+8*S*(Fintype.card (Fin 3 × Fin 3) : ℝ))*M*(CT+1)^2))*RR x*beta^n := by
      have := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left zero_le_one :
          ((8*J+8*S*(Fintype.card (Fin 3 × Fin 3) : ℝ))*M*(CT+1)^2) ≤
            1+((8*J+8*S*(Fintype.card (Fin 3 × Fin 3) : ℝ))*M*(CT+1)^2)) hc
      nlinarith [this]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientJetBounds
