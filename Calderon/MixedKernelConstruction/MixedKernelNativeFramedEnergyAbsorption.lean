import Calderon.MixedKernelConstruction.MixedKernelNativeTwoMetricLeading
import Calderon.MixedKernelConstruction.MixedKernelNativeProfileGainAbsorption
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConnectionError
open scoped InnerProductSpace

/-- Fixed packet constants yield the exact strict framed energy inequality with degree before epsilon. -/
theorem exists_native_framed_energy_strictness_parameters
    (c0 c D1 D2 D3 Cr Cg : ℝ) (hc0 : 0<c0) (hc : 0<c)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3) (hCr : 0 ≤ Cr) (hCg : 0 ≤ Cg) :
    ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p → ∃ eps0 : ℝ, 0<eps0 ∧ eps0 ≤ 1 ∧
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 → ∀ beta r : ℝ, c0*(p : ℝ) ≤ beta →
      0<r → r ≤ 1 → D1*r^2 ≤ 1/320 → D2*eps*r ≤ 1/320 →
      ∀ (T1 R1 T2 R2 : R3 →L[ℝ] R3) (z b e u w : R3),
      ‖z‖=1 → ‖b‖ ≤ 1/8 → ‖e‖ ≤ 1/8 → ‖b‖ ≤ r*beta → ‖e‖ ≤ D3*r^2 →
      ‖T1-ContinuousLinearMap.id ℝ R3‖ ≤ D1*r^2 →
      ‖T2-ContinuousLinearMap.id ℝ R3‖ ≤ D2*eps*r →
      (∀ X : R3, T1 (R1 X)=X) → (∀ X : R3, T2 (R2 X)=X) →
      ⟪z,u⟫_ℝ=0 → ⟪u,R1 u⟫_ℝ=(⟪z,T1 z⟫_ℝ)⁻¹ →
      ⟪z+(b+e),w⟫_ℝ=0 → ⟪w,R2 w⟫_ℝ=(⟪z+(b+e),T2 (z+(b+e))⟫_ℝ)⁻¹ →
      ∀ H : R3 → R3 → ℝ,
      (∀ U V : R3, ‖U-V‖^2-2*⟪b,V⟫_ℝ^2+c*beta*r^2*‖V‖^2-
        Cr*r^2*(‖U‖+‖V‖)^2-Cg*eps*r^2*‖V‖^2 ≤ H U V) →
      let q1 := (⟪z,T1 z⟫_ℝ)⁻¹ • T1 z
      let q2 := (⟪z+(b+e),T2 (z+(b+e))⟫_ℝ)⁻¹ • T2 (z+(b+e))
      0<H q1 q2+H u w := by
  let A := 1120*D1+264*D3+100*Cr
  let B := 1792*D2
  let E := 200704*D2^2
  let F := 1792*D2*D3+32*Cg
  let C := 1+A+B+E+F
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hB : 0 ≤ B := by dsimp [B];positivity
  have hE : 0 ≤ E := by dsimp [E];positivity
  have hF : 0 ≤ F := by dsimp [F];positivity
  have hC : 0<C := by dsimp [C];linarith
  have hAC : A ≤ C := by dsimp [C];linarith
  have hBC : B ≤ C := by dsimp [C];linarith
  have hEC : E ≤ C := by dsimp [C];linarith
  have hFC : F ≤ C := by dsimp [C];linarith
  obtain ⟨p0,hp0,HP⟩ := exists_native_profile_gain_absorption_parameters c0 c C hc0 hc hC
  refine ⟨p0,hp0,?_⟩
  intro p hp
  obtain ⟨eps0,heps0,heps1,HE⟩ := HP p hp
  refine ⟨eps0,heps0,heps1,?_⟩
  intro eps heps hepsCap beta r hBeta hr hr1 hEta1 hEta2 T1 R1 T2 R2 z b e u w hz hb he hbBeta heRadius hT1 hT2 hInv1 hInv2 huOrth huLength hwOrth hwLength H hH q1 q2
  have hBeta0 : 0 ≤ beta := (mul_nonneg hc0.le (Nat.cast_nonneg p)).trans hBeta
  obtain ⟨hq1,hq2,hu,hw,hq2Low,hLead⟩ := native_two_metric_leading_lower_bound T1 R1 T2 R2 z b e u w (D1*r^2) (D2*eps*r)
    hz hb he hEta1 hEta2 hT1 hT2 hInv1 hInv2 huOrth huLength hwOrth hwLength
  have hSumQ : (‖q1‖+‖q2‖)^2 ≤ 36 := by
    have hh : ‖q1‖+‖q2‖ ≤ 6 := by linarith
    simpa only [show (6 : ℝ)^2=36 by norm_num] using (sq_le_sq₀ (by positivity : 0 ≤ ‖q1‖+‖q2‖) (by norm_num : (0 : ℝ) ≤ 6)).mpr hh
  have hSumW : (‖u‖+‖w‖)^2 ≤ 64 := by
    have hh : ‖u‖+‖w‖ ≤ 8 := by linarith
    simpa only [show (8 : ℝ)^2=64 by norm_num] using (sq_le_sq₀ (by positivity : 0 ≤ ‖u‖+‖w‖) (by norm_num : (0 : ℝ) ≤ 8)).mpr hh
  have hq2Sq : ‖q2‖^2 ≤ 16 := by nlinarith only [hq2,norm_nonneg q2]
  have hwSq : ‖w‖^2 ≤ 16 := by nlinarith only [hw,norm_nonneg w]
  have hRefErr : Cr*r^2*((‖q1‖+‖q2‖)^2+(‖u‖+‖w‖)^2) ≤ 100*Cr*r^2 := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hSumQ hSumW) (mul_nonneg hCr (sq_nonneg r))
    nlinarith only [hh]
  have hConnErr : Cg*eps*r^2*(‖q2‖^2+‖w‖^2) ≤ 32*Cg*eps*r^2 := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hq2Sq hwSq) (by positivity : 0 ≤ Cg*eps*r^2)
    nlinarith only [hh]
  have hbE : ‖b+e‖ ≤ r*beta+D3*r^2 := (norm_add_le b e).trans (add_le_add hbBeta heRadius)
  have hCross : 1792*‖b+e‖*(D2*eps*r) ≤ 1792*D2*eps*beta*r^2+1792*D2*D3*eps*r^2 := by
    have hh := mul_le_mul_of_nonneg_right hbE (by positivity : 0 ≤ 1792*(D2*eps*r))
    have hr3 : r^3 ≤ r^2 := by nlinarith only [mul_le_mul_of_nonneg_right hr1 (sq_nonneg r)]
    have hh3 := mul_le_mul_of_nonneg_left hr3 (by positivity : 0 ≤ 1792*D2*D3*eps)
    nlinarith only [hh,hh3]
  have hJac := mul_le_mul_of_nonneg_left heRadius (by norm_num : (0 : ℝ) ≤ 264)
  have hLeading : -(1120*D1+264*D3)*r^2-B*eps*beta*r^2-E*eps^2*r^2-
      (1792*D2*D3)*eps*r^2 ≤ 
      ‖q1-q2‖^2+‖u-w‖^2-2*(⟪b,q2⟫_ℝ^2+⟪b,w⟫_ℝ^2) := by
    dsimp only [B,E]
    nlinarith only [hLead,hCross,hJac]
  have hGainW : 0 ≤ c*beta*r^2*‖w‖^2 := by positivity
  have hCoarse : c*beta*r^2*‖q2‖^2-A*r^2-B*eps*beta*r^2-E*eps^2*r^2-F*eps*r^2 ≤ H q1 q2+H u w := by
    have h1 := hH q1 q2
    have h2 := hH u w
    dsimp only [A,F]
    nlinarith only [h1,h2,hLeading,hRefErr,hConnErr,hGainW]
  have hALoss := mul_le_mul_of_nonneg_right hAC (sq_nonneg r)
  have hBLoss := mul_le_mul_of_nonneg_right hBC (by positivity : 0 ≤ eps*beta*r^2)
  have hELoss := mul_le_mul_of_nonneg_right hEC (by positivity : 0 ≤ eps^2*r^2)
  have hFLoss := mul_le_mul_of_nonneg_right hFC (by positivity : 0 ≤ eps*r^2)
  apply HE eps heps hepsCap beta r ‖q2‖ (H q1 q2+H u w) hBeta hr (by linarith)
  nlinarith only [hCoarse,hALoss,hBLoss,hELoss,hFLoss]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
