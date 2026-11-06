import Calderon.ActualReferenceZeroECommutators
import Calderon.ActualSecondGeometryCaps
import Calderon.ProfileRadiusJets
import Calderon.ReferenceWeightedApproximation

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceZeroEProfileCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualReferenceZeroECommutators ActualSecondGeometryCaps ReferenceDensityBounds
  AmbientReferenceRaising ConformalDepth ReferenceWeightedApproximation SmoothMetricFrame MovingFrameConnection

private lemma norm_ten_sum_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : Generator → ℝ) (A : Generator → E) (K M : ℝ) (hK : 0 ≤ K)
    (hc : ∀ V, |c V| ≤ K) (hA : ∀ V, ‖A V‖ ≤ M) :
    ‖∑ V : Generator, c V • A V‖ ≤ 10*K*M := by
  calc
    _ ≤ ∑ V : Generator, ‖c V • A V‖ := norm_sum_le _ _
    _ ≤ ∑ V : Generator, K*M := by
      apply Finset.sum_le_sum
      intro V _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hc V) (hA V) (norm_nonneg _) hK
    _ = _ := by norm_num [Generator] <;> ring

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GenRoom" => GeneratorEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CH" => pairedLeftHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "DH" => pairedRightHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "LC" => referenceLeftHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RC" => referenceRightHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "LL" => referenceLeftLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "cc" => referenceAngularZeroCoefficient g L

/-- Actual three operator norms, with one selected original low endpoint throughout. -/
def ReferenceZeroEBetaCaps (hreg : FixedDirichletRegularity) (d0 : ℝ)
    (germs : CoeffRoom d0) (d : ℝ) (room : GenRoom hreg d0 germs d) (K : Set R3) (CG : ℝ) : Prop :=
  ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, 0 < dr → dr ≤ 1 → ∀ Ar : ℝ, 0 < Ar →
    ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, (Tq dr Ar p q) x ∈ ParamRoom d →
    1 ≤ actualReferenceBeta g L q dr Ar p x → ∀ i j : Fin 3,
    ‖LC hreg d0 germs dr Ar p q x i j‖ ≤ CG*actualReferenceBeta g L q dr Ar p x ∧
    ‖RC hreg d0 germs dr Ar p q x i j‖ ≤ CG*actualReferenceBeta g L q dr Ar p x ∧
    ‖LL hreg d0 germs d room dr Ar p q x i j‖ ≤ CG*actualReferenceBeta g L q dr Ar p x

local notation "Caps" => ReferenceZeroEBetaCaps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
attribute [local irreducible] pairedLeftHigh pairedRightHigh referenceFrameConnectionCoefficient
  referenceMetricGramFrame

/-- All caps are produced by the actual packet and original geometry/profile, before every profile. -/
theorem exists_reference_zero_E_beta_caps (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (d0 : ℝ) (germs : CoeffRoom d0)
    (d : ℝ) (room : GenRoom hreg d0 germs d) (K : Set R3) (hK : IsCompact K) :
    ∃ CG : ℝ, 0 < CG ∧ Caps hreg d0 germs d room K CG := by
  obtain ⟨MG,hMG,hGcaps⟩ := room.finiteCaps 0
  obtain ⟨M,hM,hGeom⟩ := exists_geometryCaps g g hg hg L K hK
  obtain ⟨J,hJ,hJet⟩ := exists_dilated_referenceRadius_fixed_uniform_jet_envelope
    g hg L hL K hK 1
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  let C0 : ℝ := 10*M*(1+J)*MG
  have hC0 : 0 ≤ C0 := by
    dsimp only [C0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0)
      (add_nonneg zero_le_one hJ0)) hMG
  let CG : ℝ := 1+C0
  have hCG : 0 < CG := by dsimp only [CG]; linarith only [hC0]
  have hC0G : C0 ≤ CG := by dsimp only [CG]; linarith
  refine ⟨CG,hCG,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp x hx hT hb i j
  let beta : ℝ := actualReferenceBeta g L q dr Ar p x
  let ell : R3 →L[ℝ] ℝ := fderiv ℝ (fun y => Real.log (referenceRadius dr Ar p L y)) x
  let f : Fin 3 → ℝ := fun i => referenceFrameDerivative g L q i
    (fun y => Real.log (referenceRadius dr Ar p L y)) x
  let cap : ℝ := M*(1+J)*beta
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hcap0 : 0 ≤ cap := mul_nonneg
    (mul_nonneg hM0 (add_nonneg zero_le_one hJ0)) hb0
  have h1J : 1 ≤ 1+J := by linarith only [hJ0]
  have h1 : 1 ≤ (1+J)*beta := hb.trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h1J hb0)
  have hMcap : M ≤ cap := by
    simpa only [cap,mul_one,mul_assoc] using mul_le_mul_of_nonneg_left h1 hM0
  have hEll : ‖ell‖ ≤ J*beta := by
    simpa only [ell,beta,norm_iteratedFDeriv_one,pow_one,actualReferenceBeta]
      using hJet q hq dr hdr hdr1 Ar hAr p hp x hx 1 (by norm_num) (by norm_num)
  have hf (i : Fin 3) : |f i| ≤ M*J*beta := by
    rw [← Real.norm_eq_abs]
    change ‖ell (referenceMetricGramFrame g L (q,x) i)‖ ≤ M*J*beta
    calc
      _ ≤ ‖ell‖*‖referenceMetricGramFrame g L (q,x) i‖ := ell.le_opNorm _
      _ ≤ (J*beta)*M := mul_le_mul hEll ((hGeom q hq x hx).frame i)
        (norm_nonneg _) (mul_nonneg hJ0 hb0)
      _ = _ := by ring
  have hc (V : Generator) : |cc q dr Ar p x i V| ≤ cap := by
    cases V with
    | inl ab =>
      simp only [referenceAngularZeroCoefficient,abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      calc
        _ ≤ (1/2 : ℝ)*M := mul_le_mul_of_nonneg_left
          ((hGeom q hq x hx).connection i ab.2 ab.1) (by norm_num)
        _ ≤ M := by linarith only [hM0]
        _ ≤ cap := hMcap
    | inr z =>
      change |f i| ≤ cap
      exact (hf i).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : J ≤ 1+J) hM0) hb0)
  have hLeft (V : Generator) : ‖CH hreg d0 germs V j ((Tq dr Ar p q) x)‖ ≤ MG := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hGcaps V j 0 le_rfl _ hT).1
  have hRight (V : Generator) : ‖DH hreg d0 germs V j ((Tq dr Ar p q) x)‖ ≤ MG := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hGcaps V j 0 le_rfl _ hT).2.1
  have hLow (V : Generator) : ‖room.low V j ((Tq dr Ar p q) x)‖ ≤ MG := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hGcaps V j 0 le_rfl _ hT).2.2
  have hl : ‖LC hreg d0 germs dr Ar p q x i j‖ ≤ C0*beta := by
    calc
      _ ≤ 10*cap*MG := by
        change ‖∑ V : Generator, cc q dr Ar p x i V • CH hreg d0 germs V j ((Tq dr Ar p q) x)‖ ≤ _
        exact norm_ten_sum_le (E := Hi →L[ℝ] Half) (cc q dr Ar p x i)
          (fun V => CH hreg d0 germs V j ((Tq dr Ar p q) x)) cap MG hcap0 hc hLeft
      _ = _ := by dsimp only [C0,cap]; ring
  have hr : ‖RC hreg d0 germs dr Ar p q x i j‖ ≤ C0*beta := by
    calc
      _ ≤ 10*cap*MG := by
        change ‖∑ V : Generator, cc q dr Ar p x i V • DH hreg d0 germs V j ((Tq dr Ar p q) x)‖ ≤ _
        exact norm_ten_sum_le (E := Hi →L[ℝ] Half) (cc q dr Ar p x i)
          (fun V => DH hreg d0 germs V j ((Tq dr Ar p q) x)) cap MG hcap0 hc hRight
      _ = _ := by dsimp only [C0,cap]; ring
  have ho : ‖LL hreg d0 germs d room dr Ar p q x i j‖ ≤ C0*beta := by
    calc
      _ ≤ 10*cap*MG := by
        change ‖∑ V : Generator, cc q dr Ar p x i V • room.low V j ((Tq dr Ar p q) x)‖ ≤ _
        exact norm_ten_sum_le (E := Half →L[ℝ] Neg) (cc q dr Ar p x i)
          (fun V => room.low V j ((Tq dr Ar p q) x)) cap MG hcap0 hc hLow
      _ = _ := by dsimp only [C0,cap]; ring
  have hscale : C0*beta ≤ CG*beta := mul_le_mul_of_nonneg_right hC0G hb0
  exact ⟨hl.trans hscale,hr.trans hscale,ho.trans hscale⟩

/-- Producer on the exact retained W, with one room/low family and constants before profiles. -/
theorem exists_retained_reference_zero_E_beta_caps (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (d0 : ℝ) (hd0 : 0 < d0) (germs : CoeffRoom d0) (K : Set R3) (hK : IsCompact K) :
    ∃ d : ℝ, 0 < d ∧ d ≤ d0 ∧ d ≤ ρ ∧
      ∃ room : GenRoom hreg d0 germs d, ∃ CG : ℝ, 0 < CG ∧ Caps hreg d0 germs d room K CG := by
  obtain ⟨d,hd,hd0le,hdρ,_hOmega,hRoom⟩ := exists_retained_generator_paired_endpoints
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel d0 hd0 germs
  let room := Classical.choice hRoom
  obtain ⟨CG,hCG,hCaps⟩ := exists_reference_zero_E_beta_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hL hreg d0 germs d room K hK
  exact ⟨d,hd,hd0le,hdρ,room,CG,hCG,hCaps⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceZeroEProfileCaps

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceZeroEProfileCaps.exists_reference_zero_E_beta_caps
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceZeroEProfileCaps.exists_retained_reference_zero_E_beta_caps
