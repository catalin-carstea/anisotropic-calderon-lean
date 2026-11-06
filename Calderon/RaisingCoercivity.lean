import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

set_option maxHeartbeats 800000

namespace OAI.AnisotropicCalderon

theorem raising_form_lower_bound {n k c₀ c₁ C β X Y G W V F H T R₂ R₃ : ℝ}
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hC : 0 ≤ C) (hβ : 1 ≤ β) (hcsmall : c₁ ≤ c₀ / 8) (hcβ : c₁ ≤ β)
    (hcurv : 10 * C ≤ c₀ * β) (hVW : β * V ≤ W)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hG : 0 ≤ G) (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hF₁ : F ≤ k * (X + T) - H + R₂)
    (hF₂ : F ≤ (k + n - 1) * X - c₁ * Y + (2 * c₁ / β) * G + 8 * c₁ * k ^ 3 * W)
    (hT : T ≤ 0) (hH : H ≤ -2 * c₀ * k ^ 2 * W)
    (hR₂ : R₂ ≤ C * k ^ 2 * V) (hR₃ : -C * k ^ 3 * V ≤ R₃) :
    X / 2 + (c₁ / 4) * Y + c₀ * k ^ 3 * W ≤
      (2 + 2 / (k + n / 2 - 1)) * ((k + n / 2 - 1) * X - F - (k + n / 2 - 1) * H) +
        2 * G + R₃ := by
  let d := k + n / 2 - 1
  let A := 2 + 2 / d
  have hk₀ : 0 ≤ k := by linarith
  have hβ₀ : 0 < β := by linarith
  have hd : 1 ≤ d := by dsimp [d]; linarith
  have hd₀ : 0 < d := by linarith
  have hA₂ : 2 ≤ A := by
    have hh : 0 ≤ 2 / d := div_nonneg (by norm_num) hd₀.le
    dsimp [A]
    linarith
  have hA₄ : A ≤ 4 := by
    dsimp [A]
    have : 2 / d ≤ 2 := (div_le_iff₀ hd₀).mpr (by linarith)
    linarith
  have hA₀ : 0 ≤ A := by linarith
  have hb : (1 / 4 : ℝ) ≤ d - k - (n - 1) / 8 := by dsimp [d]; linarith
  have hdH : (5 / 8 : ℝ) * k ≤ d - 7 / 8 := by dsimp [d]; linarith
  have hAX : X / 2 ≤ A * (d - k - (n - 1) / 8) * X := by
    have hh : (1 / 2 : ℝ) ≤ A * (d - k - (n - 1) / 8) := by
      nlinarith [mul_nonneg (show 0 ≤ A - 2 by linarith)
        (show 0 ≤ d - k - (n - 1) / 8 - 1 / 4 by linarith)]
    nlinarith [mul_nonneg (show 0 ≤ A * (d - k - (n - 1) / 8) - 1 / 2 by linarith) hX]
  have hAY : (c₁ / 4) * Y ≤ A * (c₁ / 8) * Y := by
    nlinarith [mul_nonneg (show 0 ≤ A - 2 by linarith) (show 0 ≤ c₁ * Y by positivity)]
  have hAT : 0 ≤ -(A * (7 / 8) * k * T) := by
    have hmT : 0 ≤ -T := by linarith
    have hh : 0 ≤ A * (7 / 8) * k * (-T) := by positivity
    nlinarith only [hh]
  have hAH : (5 / 2 * c₀) * k ^ 3 * W ≤ -(A * (d - 7 / 8) * H) := by
    have hfactor : (5 / 4 : ℝ) * k ≤ A * (d - 7 / 8) := by
      nlinarith [mul_nonneg (show 0 ≤ A - 2 by linarith)
        (show 0 ≤ d - 7 / 8 by linarith)]
    have hneg : 2 * c₀ * k ^ 2 * W ≤ -H := by linarith
    have hh := mul_le_mul hfactor hneg (by positivity : 0 ≤ 2 * c₀ * k ^ 2 * W)
      (mul_nonneg hA₀ (by linarith : 0 ≤ d - 7 / 8))
    convert hh using 1 <;> ring
  have hkpow : k ^ 2 ≤ k ^ 3 := by
    calc
      k ^ 2 = k ^ 2 * 1 := by ring
      _ ≤ k ^ 2 * k := mul_le_mul_of_nonneg_left hk (sq_nonneg k)
      _ = k ^ 3 := by ring
  have hAR : A * (7 / 8) * R₂ ≤ 4 * C * k ^ 3 * V := by
    calc
      A * (7 / 8) * R₂ ≤ A * (7 / 8) * (C * k ^ 2 * V) :=
        mul_le_mul_of_nonneg_left hR₂ (by positivity)
      _ ≤ 4 * (C * k ^ 2 * V) :=
        mul_le_mul_of_nonneg_right (by linarith : A * (7 / 8) ≤ 4) (by positivity)
      _ = 4 * C * k ^ 2 * V := by ring
      _ ≤ 4 * C * k ^ 3 * V := by gcongr
  have hAC : A * c₁ * k ^ 3 * W ≤ 4 * c₁ * k ^ 3 * W := by gcongr
  have hAG : 0 ≤ (2 - A * c₁ / (4 * β)) * G := by
    have hh : A * c₁ / (4 * β) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * β)).mpr
      calc
        A * c₁ ≤ 4 * c₁ := mul_le_mul_of_nonneg_right hA₄ hc₁.le
        _ ≤ 1 * (4 * β) := by linarith
    exact mul_nonneg (by linarith) hG
  let Fmix := (7 / 8 : ℝ) * (k * (X + T) - H + R₂) +
    (1 / 8 : ℝ) * ((k + n - 1) * X - c₁ * Y + (2 * c₁ / β) * G + 8 * c₁ * k ^ 3 * W)
  have hFmix : F ≤ Fmix := by dsimp [Fmix]; linarith
  have hAF : 0 ≤ A * (Fmix - F) := mul_nonneg hA₀ (sub_nonneg.mpr hFmix)
  have hid : A * (d * X - F - d * H) + 2 * G + R₃ =
      A * (d - k - (n - 1) / 8) * X + A * (c₁ / 8) * Y - A * (7 / 8) * k * T -
      A * (d - 7 / 8) * H - A * (7 / 8) * R₂ - A * c₁ * k ^ 3 * W +
      (2 - A * c₁ / (4 * β)) * G + R₃ + A * (Fmix - F) := by
    dsimp [Fmix]
    ring
  have hbound : X / 2 + (c₁ / 4) * Y + ((5 / 2) * c₀ - 4 * c₁) * k ^ 3 * W -
      5 * C * k ^ 3 * V ≤ A * (d * X - F - d * H) + 2 * G + R₃ := by
    rw [hid]
    linarith only [hAX, hAY, hAT, hAH, hAR, hAC, hAG, hAF, hR₃]
  have hcurvloss : 5 * C * V ≤ c₀ / 2 * W := by
    have hh := mul_le_mul_of_nonneg_right hcurv hV
    have hv := mul_le_mul_of_nonneg_left hVW hc₀.le
    nlinarith only [hh, hv]
  have hremaining : c₀ * k ^ 3 * W ≤
      ((5 / 2) * c₀ - 4 * c₁) * k ^ 3 * W - 5 * C * k ^ 3 * V := by
    have hh := mul_le_mul_of_nonneg_left hcurvloss (pow_nonneg hk₀ 3)
    have hc : c₀ ≤ (5 / 2) * c₀ - 4 * c₁ - c₀ / 2 := by linarith
    have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ k ^ 3 * W)
    nlinarith only [hh, hm]
  change X / 2 + (c₁ / 4) * Y + c₀ * k ^ 3 * W ≤ A * (d * X - F - d * H) + 2 * G + R₃
  linarith

end OAI.AnisotropicCalderon
#print axioms OAI.AnisotropicCalderon.raising_form_lower_bound
