import Calderon.ReferenceDensityBounds
import Calderon.ScalarDensityAdjoint

noncomputable section
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.PerturbedDensityAdjoint
open PrincipalCommutator ScalarBaseAdjoint ReferenceDensityBounds

def TwoJetBound (i j : R3) (f : R3 → ℝ) (x : R3) (A : ℝ) : Prop :=
  |f x| ≤ A ∧ |directionalFDeriv i f x| ≤ A ∧
    |directionalFDeriv j f x| ≤ A ∧
      |directionalFDeriv j (directionalFDeriv i f) x| ≤ A

lemma directional_mul (i : R3) (f g : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : R3) :
    directionalFDeriv i (fun y => f y * g y) x =
      directionalFDeriv i f x * g x + f x * directionalFDeriv i g x := by
  simpa only [smul_eq_mul] using directionalFDeriv_smul i f g hf hg x

lemma directional_second_mul (i j : R3) (f g : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : R3) :
    directionalFDeriv j (directionalFDeriv i (fun y => f y * g y)) x =
      directionalFDeriv j (directionalFDeriv i f) x * g x +
      directionalFDeriv i f x * directionalFDeriv j g x +
      directionalFDeriv j f x * directionalFDeriv i g x +
      f x * directionalFDeriv j (directionalFDeriv i g) x := by
  simpa only [smul_eq_mul] using directionalFDeriv_second_smul i j f g hf hg x

lemma directional_second_add (i j : R3) (f g : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : R3) :
    directionalFDeriv j (directionalFDeriv i (fun y => f y + g y)) x =
      directionalFDeriv j (directionalFDeriv i f) x +
        directionalFDeriv j (directionalFDeriv i g) x := by
  have he : directionalFDeriv i (fun y => f y + g y) =
      fun y => directionalFDeriv i f y + directionalFDeriv i g y :=
    funext (directionalFDeriv_add i f g hf hg)
  rw [he, directionalFDeriv_add j _ _ (contDiff_directionalFDeriv i f hf)
    (contDiff_directionalFDeriv i g hg)]

lemma twoJetBound_mono (i j : R3) (f : R3 → ℝ) (x : R3) (A B : ℝ)
    (h : TwoJetBound i j f x A) (hab : A ≤ B) : TwoJetBound i j f x B :=
  ⟨h.1.trans hab,h.2.1.trans hab,h.2.2.1.trans hab,h.2.2.2.trans hab⟩

lemma twoJetBound_add (i j : R3) (f g : R3 → ℝ) (x : R3) (A B : ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hF : TwoJetBound i j f x A) (hG : TwoJetBound i j g x B) :
    TwoJetBound i j (fun y => f y + g y) x (A+B) := by
  refine ⟨(abs_add_le _ _).trans (add_le_add hF.1 hG.1),?_,?_,?_⟩
  · rw [directionalFDeriv_add i f g hf hg]
    exact (abs_add_le _ _).trans (add_le_add hF.2.1 hG.2.1)
  · rw [directionalFDeriv_add j f g hf hg]
    exact (abs_add_le _ _).trans (add_le_add hF.2.2.1 hG.2.2.1)
  · rw [directional_second_add i j f g hf hg]
    exact (abs_add_le _ _).trans (add_le_add hF.2.2.2 hG.2.2.2)

lemma product_two_jet_bounds (i j : R3) (f g : R3 → ℝ) (x : R3) (A B : ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : TwoJetBound i j f x A) (hG : TwoJetBound i j g x B) :
    |f x*g x|≤A*B ∧
    |directionalFDeriv i (fun y => f y*g y) x|≤2*A*B ∧
    |directionalFDeriv j (fun y => f y*g y) x|≤2*A*B ∧
    |directionalFDeriv j (directionalFDeriv i (fun y => f y*g y)) x|≤4*A*B := by
  have mulbound (v w : ℝ) (hv : |v|≤A) (hw : |w|≤B) : |v*w|≤A*B := by
    rw [abs_mul]
    exact mul_le_mul hv hw (abs_nonneg w) hA
  refine ⟨mulbound _ _ hF.1 hG.1,?_,?_,?_⟩
  · rw [directional_mul i f g hf hg]
    have h1 := mulbound _ _ hF.2.1 hG.1
    have h2 := mulbound _ _ hF.1 hG.2.1
    nlinarith [abs_add_le (directionalFDeriv i f x*g x) (f x*directionalFDeriv i g x)]
  · rw [directional_mul j f g hf hg]
    have h1 := mulbound _ _ hF.2.2.1 hG.1
    have h2 := mulbound _ _ hF.1 hG.2.2.1
    nlinarith [abs_add_le (directionalFDeriv j f x*g x) (f x*directionalFDeriv j g x)]
  · rw [directional_second_mul i j f g hf hg]
    have h1 := mulbound _ _ hF.2.2.2 hG.1
    have h2 := mulbound _ _ hF.2.1 hG.2.2.1
    have h3 := mulbound _ _ hF.2.2.1 hG.2.1
    have h4 := mulbound _ _ hF.1 hG.2.2.2
    have habs (a b c d : ℝ) : |a+b+c+d|≤|a|+|b|+|c|+|d| := by
      nlinarith [abs_add_le a b, abs_add_le (a+b) c, abs_add_le (a+b+c) d]
    exact (habs _ _ _ _).trans (by nlinarith)

def principalEntry (r q h : R3 → ℝ) (x : R3) : ℝ := r x * (q x+h x)

def densityPrincipalEntry (mu r q h : R3 → ℝ) (x : R3) : ℝ :=
  mu x * principalEntry r q h x

theorem density_principal_first_second_bounds (i j : R3) (mu r q h : R3 → ℝ)
    (hm : ContDiff ℝ ∞ mu) (hr : ContDiff ℝ ∞ r)
    (hq : ContDiff ℝ ∞ q) (hh : ContDiff ℝ ∞ h) (x : R3)
    (M J1 J2 beta eps : ℝ) (hM : 1≤M) (hJ1 : 0≤J1) (hJ2 : 0≤J2)
    (hb : 1≤beta) (heps : 0≤eps) (heps1 : eps≤1) (hpos : 0<r x)
    (hsmall : r x*beta^2≤eps)
    (hmjet : TwoJetBound i j mu x M) (hqjet : TwoJetBound i j q x M)
    (hhjet : TwoJetBound i j h x (eps*r x))
    (hr1i : |directionalFDeriv i r x|≤J1*r x*beta)
    (hr1j : |directionalFDeriv j r x|≤J1*r x*beta)
    (hr2 : |directionalFDeriv j (directionalFDeriv i r) x|≤J2*r x*beta^2) :
    |directionalFDeriv i (densityPrincipalEntry mu r q h) x|≤
      (J1+2)*M*(M+1)*eps/beta ∧
    |directionalFDeriv j (directionalFDeriv i (densityPrincipalEntry mu r q h)) x|≤
      (J2+4*J1+4)*M*(M+1)*eps := by
  have hbeta : 0<beta := by linarith
  have hM0 : 0≤M := by linarith
  have hr0 : 0≤r x := hpos.le
  have hre : r x≤eps := by nlinarith [sq_nonneg (beta-1)]
  have hepr : eps*r x≤1 := by nlinarith
  have hh1 := twoJetBound_mono i j h x _ 1 hhjet hepr
  have hsum := twoJetBound_add i j q h x M 1 hq hh hqjet hh1
  let b : R3 → ℝ := fun y => mu y*(q y+h y)
  have hbS : ContDiff ℝ ∞ b := hm.mul (hq.add hh)
  obtain ⟨hb0,hbi,hbj,hb2⟩ := product_two_jet_bounds i j mu (fun y => q y+h y) x
    M (M+1) hm (hq.add hh) hM0 (by linarith) hmjet hsum
  have he : densityPrincipalEntry mu r q h = fun y => r y*b y := by
    funext y
    unfold densityPrincipalEntry principalEntry b
    ring
  rw [he]
  have hfirst : |directionalFDeriv i (fun y => r y*b y) x|≤
      (J1+2)*M*(M+1)*(r x*beta) := by
    rw [directional_mul i r b hr hbS]
    have h1 : |directionalFDeriv i r x*b x|≤(J1*r x*beta)*(M*(M+1)) := by
      rw [abs_mul]
      exact mul_le_mul hr1i hb0 (abs_nonneg _) (by positivity)
    have h2 : |r x*directionalFDeriv i b x|≤r x*(2*M*(M+1)) := by
      rw [abs_mul,abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_left hbi hr0
    have hlow : r x*(2*M*(M+1))≤r x*beta*(2*M*(M+1)) := by
      nlinarith [mul_nonneg hr0 (show 0≤2*M*(M+1) by positivity)]
    nlinarith [abs_add_le (directionalFDeriv i r x*b x) (r x*directionalFDeriv i b x)]
  have hsecond : |directionalFDeriv j (directionalFDeriv i (fun y => r y*b y)) x|≤
      (J2+4*J1+4)*M*(M+1)*(r x*beta^2) := by
    rw [directional_second_mul i j r b hr hbS]
    have h1 : |directionalFDeriv j (directionalFDeriv i r) x*b x|≤
        (J2*r x*beta^2)*(M*(M+1)) := by
      rw [abs_mul]
      exact mul_le_mul hr2 hb0 (abs_nonneg _) (by positivity)
    have h2 : |directionalFDeriv i r x*directionalFDeriv j b x|≤
        (J1*r x*beta)*(2*M*(M+1)) := by
      rw [abs_mul]
      exact mul_le_mul hr1i hbj (abs_nonneg _) (by positivity)
    have h3 : |directionalFDeriv j r x*directionalFDeriv i b x|≤
        (J1*r x*beta)*(2*M*(M+1)) := by
      rw [abs_mul]
      exact mul_le_mul hr1j hbi (abs_nonneg _) (by positivity)
    have h4 : |r x*directionalFDeriv j (directionalFDeriv i b) x|≤
        r x*(4*M*(M+1)) := by
      rw [abs_mul,abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_left hb2 hr0
    have hlow : r x*beta≤r x*beta^2 := by nlinarith [mul_nonneg hr0 (show 0≤beta*(beta-1) by positivity)]
    have hlow2 : r x≤r x*beta^2 := by nlinarith [sq_nonneg (beta-1)]
    have hh2 := mul_le_mul_of_nonneg_left hlow (show 0≤2*J1*M*(M+1) by positivity)
    have hh4 := mul_le_mul_of_nonneg_left hlow2 (show 0≤4*M*(M+1) by positivity)
    have habs (a b c d : ℝ) : |a+b+c+d|≤|a|+|b|+|c|+|d| := by
      nlinarith [abs_add_le a b,abs_add_le (a+b) c,abs_add_le (a+b+c) d]
    have ht := habs (directionalFDeriv j (directionalFDeriv i r) x*b x)
      (directionalFDeriv i r x*directionalFDeriv j b x)
      (directionalFDeriv j r x*directionalFDeriv i b x)
      (r x*directionalFDeriv j (directionalFDeriv i b) x)
    nlinarith
  constructor
  · have hs : r x*beta≤eps/beta := (le_div_iff₀ hbeta).mpr (by nlinarith [hsmall])
    have ht := mul_le_mul_of_nonneg_left hs (show 0≤(J1+2)*M*(M+1) by positivity)
    exact hfirst.trans (by simpa only [mul_div_assoc] using ht)
  · exact hsecond.trans (mul_le_mul_of_nonneg_left hsmall
      (show 0≤(J2+4*J1+4)*M*(M+1) by positivity))

end OAI.AnisotropicCalderon.PerturbedDensityAdjoint
