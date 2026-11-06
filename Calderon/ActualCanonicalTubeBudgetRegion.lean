import Calderon.ActualUniformTubeCompactBandSupremum
import Calderon.ActualMixedKernelConstruction
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

def unseededTubeBand (M e0 sigma c0 B T0 amin amax:ℝ):Set (R3×R3) :=
  (fun q:ℝ×R3×R3 => (q.2.1+tubeRadius M e0 q.1 sigma q.2.1 • q.2.2,q.2.1)) ''
    {q:ℝ×R3×R3 | ‖q.2.2‖=1 ∧ -B-1 ≤ q.2.1 2 ∧ tubeHeight M e0 q.2.1 ≤ T0 ∧
      amin ≤ q.1 ∧ q.1 ≤ amax ∧ c0*‖(q.2.1+tubeRadius M e0 q.1 sigma q.2.1 • q.2.2)-q.2.1‖ ≤
        min ((q.2.1+tubeRadius M e0 q.1 sigma q.2.1 • q.2.2) 2) (q.2.1 2)}

def interiorTubeRoom (M e0 B T0 CY lower upper:ℝ):Set (R3×R3) :=
  tubeChartRoom {Y:R3 | ‖Y‖ < CY ∧ 0 < tubeHeight M e0 Y} lower upper ∩
    {z:R3×R3 | -B-1 < z.2 2 ∧ tubeHeight M e0 z.2 < T0}

def interiorTubeSeed (M e0 c0 B T0 CY lower upper:ℝ):Set (R3×R3) :=
  {z | z∈interiorTubeRoom M e0 B T0 CY lower upper ∧ min (z.1 2) (z.2 2) < c0*‖z.1-z.2‖}

theorem isCompact_unseededTubeBand (M e0 sigma c0 B T0 amin amax:ℝ) (hsigma:0 ≤ sigma) (he0:0 < e0):
    IsCompact (unseededTubeBand M e0 sigma c0 B T0 amin amax) := by
  exact (tubeSweep_isCompact M e0 sigma c0 B T0 amin amax hsigma he0).image
    ((tubeEndpoint_continuous M e0 sigma hsigma).prodMk continuous_snd.fst)

theorem isOpen_interiorTubeRoom_and_seed (M e0 c0 B T0 CY lower upper:ℝ):
    IsOpen (interiorTubeRoom M e0 B T0 CY lower upper) ∧ IsOpen (interiorTubeSeed M e0 c0 B T0 CY lower upper) := by
  have hP:IsOpen {Y:R3 | ‖Y‖ < CY ∧ 0 < tubeHeight M e0 Y} :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const (st_height_continuous M e0))
  have hY:Continuous (fun z:R3×R3 => z.2 2) := (EuclideanSpace.proj (𝕜:=ℝ) (2:Fin 3)).continuous.comp continuous_snd
  have hU:IsOpen (interiorTubeRoom M e0 B T0 CY lower upper) :=
    (tubeChartRoom_isOpen hP lower upper).inter ((isOpen_lt continuous_const hY).inter
      (isOpen_lt ((st_height_continuous M e0).comp continuous_snd) continuous_const))
  have hMin:Continuous (fun z:R3×R3 => min (z.1 2) (z.2 2)) :=
    ((EuclideanSpace.proj (𝕜:=ℝ) (2:Fin 3)).continuous.comp continuous_fst).min hY
  exact ⟨hU,hU.inter (isOpen_lt hMin (continuous_const.mul (continuous_fst.sub continuous_snd).norm))⟩

theorem unseededTubeBand_radialLevel_bounds (M e0 sigma c0 B T0 amin amax:ℝ)
    (he0:0 ≤ e0) (hM:B+3 < M) (hamin:0 < amin):
    ∀ p∈unseededTubeBand M e0 sigma c0 B T0 amin amax,
      amin ≤ tubeRadialLevel M e0 sigma p ∧ tubeRadialLevel M e0 sigma p ≤ amax := by
  rintro p ⟨⟨a,Y,w⟩,⟨hw,hY,hT,ha1,ha2,hsep⟩,rfl⟩
  have ht1:1 ≤ tubeHeight M e0 Y := (tube_base_height he0 hM hY hT).1
  have ht:0 < tubeHeight M e0 Y := zero_lt_one.trans_le ht1
  have hL:tubeRadialLevel M e0 sigma (Y+tubeRadius M e0 a sigma Y • w,Y)=a :=
    tube_front_level (hamin.le.trans ha1) ht hw
  rw [hL]
  exact ⟨ha1,ha2⟩

theorem unseededTubeBand_subset_interiorTubeRoom
    (M e0 sigma c0 B T0 amin CY lower upper:ℝ)
    (hc0:0 < c0) (hB:0 ≤ B) (hM:B+3 < M) (he0:0 ≤ e0) (hsigma:0 ≤ sigma) (hsigma1:sigma ≤ 1)
    (hamin:0 < amin) (hlower:lower < amin) (hupper:(2/c0+1)*max 1 T0^2 < upper)
    (hTop:1 < c0*amin*T0^sigma)
    (hCenter:∀ Y:R3,-B-1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 → ‖Y‖ < CY):
    unseededTubeBand M e0 sigma c0 B T0 amin (2/c0+1)⊆interiorTubeRoom M e0 B T0 CY lower upper := by
  rintro p ⟨⟨a,Y,w⟩,⟨hw,hY,hT,ha1,ha2,hsep⟩,rfl⟩
  have ht1:1 ≤ tubeHeight M e0 Y := (tube_base_height he0 hM hY hT).1
  have ht:0 < tubeHeight M e0 Y := zero_lt_one.trans_le ht1
  have ha:0 < a := hamin.trans_le ha1
  have hr:0 < tubeRadius M e0 a sigma Y := mul_pos ha (Real.rpow_pos_of_pos ht _)
  have hNoCone:¬min ((Y+tubeRadius M e0 a sigma Y • w) 2) (Y 2) < c0*‖(Y+tubeRadius M e0 a sigma Y • w)-Y‖ := not_lt.mpr hsep
  have hRoom:=tube_front_in_room hamin hlower hupper ha1 ha2 hsigma hsigma1 ht1 hT
    (show Y∈{Y:R3 | ‖Y‖ < CY ∧ 0 < tubeHeight M e0 Y} from ⟨hCenter Y hY hT,ht⟩) hw
  refine ⟨hRoom,?_,?_⟩
  · by_contra hn
    have hyNeg:Y 2 < 0 := by have hh:=le_of_not_gt hn;linarith only [hh,hB]
    exact hNoCone (tube_bottom_face_in_seed hc0 hr hyNeg hw)
  · by_contra hn
    have htEq:tubeHeight M e0 Y=T0 := le_antisymm hT (le_of_not_gt hn)
    have hTopAt:1 < c0*amin*tubeHeight M e0 Y^sigma := by rw [htEq];exact hTop
    have hMpos:0 < M := by linarith only [hM,hB]
    exact hNoCone (tube_top_face_in_seed hc0 hMpos.le he0 ht hamin.le ha1 hTopAt hw)

theorem unseededTubeBand_flat_strictness
    (M e0 sigma c0 B T0 amin amax:ℝ) (he0:0 ≤ e0) (hM:B+3 < M) (hamin:0 < amin)
    (hStrict:∀ a:ℝ,∀ Y w:R3,‖w‖=1 → -B-1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      amin ≤ a → a ≤ amax → ¬min ((Y+tubeRadius M e0 a sigma Y • w) 2) (Y 2) <
        c0*‖(Y+tubeRadius M e0 a sigma Y • w)-Y‖ →
      ProductHessianStrictAt (fun _:R3 => (1:Matrix (Fin 3) (Fin 3) ℝ))
        (fun _:R3 => (1:Matrix (Fin 3) (Fin 3) ℝ)) (Y+tubeRadius M e0 a sigma Y • w) Y (tubePhase M e0 a sigma)):
    ∀ p∈unseededTubeBand M e0 sigma c0 B T0 amin amax,
      ProductHessianStrictAt (fun _:R3 => (1:Matrix (Fin 3) (Fin 3) ℝ))
        (fun _:R3 => (1:Matrix (Fin 3) (Fin 3) ℝ)) p.1 p.2 (tubePhase M e0 (tubeRadialLevel M e0 sigma p) sigma) := by
  rintro p ⟨⟨a,Y,w⟩,⟨hw,hY,hT,ha1,ha2,hsep⟩,rfl⟩
  have ht:0 < tubeHeight M e0 Y := zero_lt_one.trans_le (tube_base_height he0 hM hY hT).1
  have hL:tubeRadialLevel M e0 sigma (Y+tubeRadius M e0 a sigma Y • w,Y)=a :=
    tube_front_level (hamin.le.trans ha1) ht hw
  rw [hL]
  exact hStrict a Y w hw hY hT ha1 ha2 (not_lt.mpr hsep)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
