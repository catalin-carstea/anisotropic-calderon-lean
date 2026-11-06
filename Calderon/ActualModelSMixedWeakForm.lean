import Calderon.ActualModelSMixedIntegral

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualModelSMixedComparison
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints
  ReferenceDensityBounds FixedParameterProfilePullback FixedParameterProfileBudgets

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
  (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
  (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)

local notation "MR" => nativeModelRaising hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "MD" => nativeModelAdjoint hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "ZZ" => nativeZ hO hD hF g hg L q dr Ar p hdr hAr
local notation "SO" => ActualHigherSFormation.nativeHigherSOut
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
  dr Ar p hdr hAr q hreg data.δ0 data.germs g2
local notation "SD" => ActualHigherSAdjointFormation.higherSAdjointOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  hreg data.δ0 data.germs g2 dr Ar p hdr hAr q

local notation "TF" => nativeT hO hD hF g hg L q dr Ar p hdr hAr
local notation "TD" => nativeTdag hO hD hF g hg L q dr Ar p hdr hAr
local notation "UF" => nativeU hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "UD" => nativeUdag hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "CRoom" δ:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "Tq" => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)


/-- Literal weak mixed operator for finite model outputs; S outputs remain unrestricted. -/
def actualModelSMixedWeakOut (A Bf : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  SD A x-SO Bf x

include hg2 in
/-- Genuine S adjunction for independent finite model outputs in the same original room.
Room premises for model compositions are discharged by separate locality lemmas. -/
theorem actual_model_S_mixed_weak_identity_of_common_room
    (δ : ℝ) (Cm : CRoom δ)
    (F A Bf : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, Tq x ∈ ParamRoom δ)
    (hTA : ∀ x ∈ tsupport A.val, Tq x ∈ ParamRoom δ)
    (hTB : ∀ x ∈ tsupport Bf.val, Tq x ∈ ParamRoom δ) :
    let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
    Integrable (fun x => mu x*(⟪A.val x,SO F x⟫_ℝ-⟪Bf.val x,SD F x⟫_ℝ)) ∧
    Integrable (fun x => mu x*⟪F.val x,
      actualModelSMixedWeakOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 dr Ar p hdr hAr q A Bf x⟫_ℝ) ∧
    (∫ x, mu x*(⟪A.val x,SO F x⟫_ℝ-⟪Bf.val x,SD F x⟫_ℝ)) =
      ∫ x, mu x*⟪F.val x,
        actualModelSMixedWeakOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          Room hreg data g2 dr Ar p hdr hAr q A Bf x⟫_ℝ := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  have hA := ActualHigherSAdjointFormation.integrated_higherS_physical_adjoint
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm g2 hg2 dr Ar p hdr hAr q A F hTA hTF
  have hB := ActualHigherSAdjointFormation.integrated_higherS_physical_adjoint
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm g2 hg2 dr Ar p hdr hAr q F Bf hTF hTB
  have hR : Integrable (fun x => mu x*⟪Bf.val x,SD F x⟫_ℝ) :=
    hB.2.1.congr (Filter.Eventually.of_forall (fun x => by dsimp only [mu]; rw [real_inner_comm]))
  have hL : Integrable (fun x => mu x*⟪F.val x,SD A x⟫_ℝ) :=
    hA.2.1.congr (Filter.Eventually.of_forall (fun x => by dsimp only [mu]; rw [real_inner_comm]))
  have hLeft := weighted_difference_integral mu (fun x => ⟪A.val x,SO F x⟫_ℝ)
    (fun x => ⟪Bf.val x,SD F x⟫_ℝ) hA.1 hR
  have hRight := weighted_difference_integral mu (fun x => ⟪F.val x,SD A x⟫_ℝ)
    (fun x => ⟪F.val x,SO Bf x⟫_ℝ) hL hB.1
  have eWeak : (fun x => mu x*⟪F.val x,
      actualModelSMixedWeakOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 dr Ar p hdr hAr q A Bf x⟫_ℝ) =
      (fun x => mu x*(⟪F.val x,SD A x⟫_ℝ-⟪F.val x,SO Bf x⟫_ℝ)) := by
    funext x
    dsimp only [actualModelSMixedWeakOut]
    rw [inner_sub_right]
  have hWeak : Integrable (fun x => mu x*⟪F.val x,
      actualModelSMixedWeakOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 dr Ar p hdr hAr q A Bf x⟫_ℝ) :=
    Eq.mpr (congrArg (fun f : R3 → ℝ => Integrable f) eWeak) hRight.1
  have eqA : (∫ x, mu x*⟪A.val x,SO F x⟫_ℝ) =
      ∫ x, mu x*⟪F.val x,SD A x⟫_ℝ := by
    calc
      _ = ∫ x, mu x*⟪SD A x,F.val x⟫_ℝ := hA.2.2
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun x => by dsimp only [mu]; rw [real_inner_comm]))
  have eqB : (∫ x, mu x*⟪Bf.val x,SD F x⟫_ℝ) =
      ∫ x, mu x*⟪F.val x,SO Bf x⟫_ℝ := by
    calc
      _ = ∫ x, mu x*⟪SD F x,Bf.val x⟫_ℝ :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => by dsimp only [mu]; rw [real_inner_comm]))
      _ = _ := hB.2.2.symm
  refine ⟨hLeft.1,hWeak,?_⟩
  calc
    _ = (∫ x, mu x*⟪A.val x,SO F x⟫_ℝ)-(∫ x, mu x*⟪Bf.val x,SD F x⟫_ℝ) := hLeft.2
    _ = (∫ x, mu x*⟪F.val x,SD A x⟫_ℝ)-(∫ x, mu x*⟪F.val x,SO Bf x⟫_ℝ) := congrArg₂ (fun a b : ℝ => a-b) eqA eqB
    _ = ∫ x, mu x*(⟪F.val x,SD A x⟫_ℝ-⟪F.val x,SO Bf x⟫_ℝ) := hRight.2.symm
    _ = _ := (congrArg (fun f : R3 → ℝ => ∫ x, f x) eWeak).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualModelSMixedComparison
