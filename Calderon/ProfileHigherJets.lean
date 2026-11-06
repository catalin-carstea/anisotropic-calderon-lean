import Calderon.ProfileUniform
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.RadiusProfile

def logistic (z : ℝ) : ℝ := Real.exp z / (1 + Real.exp z)

def logisticComplement (z : ℝ) : ℝ := 1 / (1 + Real.exp z)

def logExp (z : ℝ) : ℝ := Real.log (1 + Real.exp z)

lemma logistic_pos (z : ℝ) : 0 < logistic z := by
  unfold logistic
  positivity

lemma logisticComplement_pos (z : ℝ) : 0 < logisticComplement z := by
  unfold logisticComplement
  positivity

lemma logistic_add_complement (z : ℝ) : logistic z + logisticComplement z = 1 := by
  unfold logistic logisticComplement
  field_simp
  <;> ring

lemma logistic_lt_one (z : ℝ) : logistic z < 1 := by
  linarith [logistic_add_complement z, logisticComplement_pos z]

lemma logisticComplement_lt_one (z : ℝ) : logisticComplement z < 1 := by
  linarith [logistic_add_complement z, logistic_pos z]

lemma logExp_pos (z : ℝ) : 0 < logExp z := log_exp_add_one_pos z

lemma logisticComplement_eq_exp_neg (z : ℝ) :
    logisticComplement z = Real.exp (-logExp z) := by
  unfold logisticComplement logExp
  rw [Real.exp_neg, Real.exp_log (by positivity)]
  simp only [one_div]

lemma hasDerivAt_logistic (z : ℝ) :
    HasDerivAt logistic (logistic z * logisticComplement z) z := by
  have he := Real.hasDerivAt_exp z
  have h := he.div ((hasDerivAt_const z (1 : ℝ)).add he) (by positivity : 1 + Real.exp z ≠ 0)
  convert! h using 1 <;> simp [logistic, logisticComplement]
  field_simp
  <;> ring

lemma hasDerivAt_logisticComplement (z : ℝ) :
    HasDerivAt logisticComplement (-logistic z * logisticComplement z) z := by
  have h := (hasDerivAt_const z (1 : ℝ)).div
    ((hasDerivAt_const z (1 : ℝ)).add (Real.hasDerivAt_exp z)) (by positivity : 1 + Real.exp z ≠ 0)
  convert! h using 1 <;> simp [logistic, logisticComplement]
  field_simp
  <;> ring

lemma hasDerivAt_logExp (z : ℝ) : HasDerivAt logExp (logistic z) z := by
  have h := ((hasDerivAt_const z (1 : ℝ)).add (Real.hasDerivAt_exp z)).log
    (by positivity : 1 + Real.exp z ≠ 0)
  change HasDerivAt (fun y => Real.log (1 + Real.exp y)) (Real.exp z / (1 + Real.exp z)) z
  simpa only [Pi.add_apply, zero_add] using h

lemma logExp_le_two_mul_logistic (z : ℝ) (hq : logistic z ≤ 1 / 2) :
    logExp z ≤ 2 * logistic z := by
  have hlog : logExp z ≤ Real.exp z := by
    unfold logExp
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + Real.exp z)
    linarith
  have hw : 1 / 2 ≤ logisticComplement z := by
    linarith [logistic_add_complement z]
  have he : Real.exp z * logisticComplement z = logistic z := by
    unfold logistic logisticComplement
    ring
  have hmul := mul_le_mul_of_nonneg_left hw (Real.exp_pos z).le
  nlinarith

lemma logExp_pow_mul_complement_le_factorial (z : ℝ) (n : ℕ) :
    logExp z ^ n * logisticComplement z ≤ (n.factorial : ℝ) := by
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (logExp z) (logExp_pos z).le n)
  have he : Real.exp (logExp z) * logisticComplement z = 1 := by
    unfold logExp logisticComplement
    rw [Real.exp_log (by positivity)]
    field_simp
  have hm := mul_le_mul_of_nonneg_right h (logisticComplement_pos z).le
  nlinarith

/-- The finite terms in the normalized derivative numerator. -/
structure ProfileJetTerm where
  coeff : ℝ
  qPower : ℕ
  complementPower : ℕ
  logPower : ℕ

def ProfileJetTerm.value (t : ProfileJetTerm) (z : ℝ) : ℝ :=
  t.coeff * logistic z ^ t.qPower * logisticComplement z ^ t.complementPower *
    logExp z ^ t.logPower

def ProfileJetTerm.admissible (t : ProfileJetTerm) (j : ℕ) : Prop :=
  t.coeff ≠ 0 → j ≤ t.qPower + t.logPower ∧
    (0 < t.logPower → 0 < t.complementPower)

def ProfileJetTerm.next (j : ℕ) (t : ProfileJetTerm) : List ProfileJetTerm :=
  [⟨t.coeff * t.qPower, t.qPower, t.complementPower + 1, t.logPower + 1⟩,
   ⟨-t.coeff * t.complementPower, t.qPower + 1, t.complementPower, t.logPower + 1⟩,
   ⟨t.coeff * ((t.logPower : ℝ) - j), t.qPower + 1, t.complementPower, t.logPower⟩]

lemma ProfileJetTerm.admissible_next (t : ProfileJetTerm) (j : ℕ)
    (ht : t.admissible j) : ∀ s ∈ t.next j, s.admissible (j + 1) := by
  intro s hs
  simp only [ProfileJetTerm.next, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · intro hn
    dsimp only at hn ⊢
    have hc : t.coeff ≠ 0 := by intro h; simp [h] at hn
    obtain ⟨ha, hb⟩ := ht hc
    exact ⟨by omega, by omega⟩
  · intro hn
    dsimp only at hn ⊢
    have hc : t.coeff ≠ 0 := by intro h; simp [h] at hn
    have hb : 0 < t.complementPower := by
      by_contra h
      have hz : t.complementPower = 0 := by omega
      simp [hz] at hn
    obtain ⟨ha, _⟩ := ht hc
    exact ⟨by omega, fun _ => hb⟩
  · intro hn
    dsimp only at hn ⊢
    have hc : t.coeff ≠ 0 := by intro h; simp [h] at hn
    obtain ⟨ha, hb⟩ := ht hc
    exact ⟨by omega, hb⟩

lemma profile_jet_monomial_bound (z : ℝ) (a b c j : ℕ)
    (hdegree : j ≤ a + c) (hlog : 0 < c → 0 < b) :
    logistic z ^ a * logisticComplement z ^ b * logExp z ^ c ≤
      (2 : ℝ) ^ (c + j) * (c.factorial : ℝ) * logistic z ^ j := by
  have hq0 := (logistic_pos z).le
  have hw0 := (logisticComplement_pos z).le
  have hq1 := (logistic_lt_one z).le
  have hw1 := (logisticComplement_lt_one z).le
  have hqp : logistic z ^ a ≤ 1 := pow_le_one₀ hq0 hq1
  have hwp : logisticComplement z ^ b ≤ 1 := pow_le_one₀ hw0 hw1
  have hcFact : (1 : ℝ) ≤ c.factorial := by exact_mod_cast Nat.factorial_pos c
  have htwo : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  by_cases hsmall : logistic z ≤ 1 / 2
  · have hL := pow_le_pow_left₀ (logExp_pos z).le
      (logExp_le_two_mul_logistic z hsmall) c
    have hdegree' : logistic z ^ (a + c) ≤ logistic z ^ j :=
      pow_le_pow_of_le_one hq0 hq1 hdegree
    have hm := mul_le_mul_of_nonneg_left hL
      (show 0 ≤ logistic z ^ a * logisticComplement z ^ b by positivity)
    have hw := mul_le_mul_of_nonneg_left hwp
      (show 0 ≤ logistic z ^ a * (2 * logistic z) ^ c by positivity)
    have hbase : logistic z ^ a * logisticComplement z ^ b * logExp z ^ c ≤
        2 ^ c * logistic z ^ (a + c) := by
      calc
        _ ≤ logistic z ^ a * logisticComplement z ^ b * (2 * logistic z) ^ c := hm
        _ ≤ logistic z ^ a * (2 * logistic z) ^ c := by nlinarith [hw]
        _ = _ := by rw [mul_pow, pow_add]; ring
    have hfirst := mul_le_mul_of_nonneg_left hdegree' (show 0 ≤ (2 : ℝ) ^ c by positivity)
    have hbig : (2 : ℝ) ^ c ≤ 2 ^ (c + j) * c.factorial := by
      rw [pow_add]
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) c,
        mul_le_mul htwo hcFact (by norm_num) (by positivity : (0 : ℝ) ≤ 2 ^ j)]
    exact hbase.trans (hfirst.trans (mul_le_mul_of_nonneg_right hbig (by positivity)))
  · have hhalf : (1 / 2 : ℝ) ≤ logistic z := le_of_not_ge hsmall
    have hqj := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf j
    have hj : (1 : ℝ) ≤ 2 ^ j * logistic z ^ j := by
      have hh := mul_le_mul_of_nonneg_left hqj (show (0 : ℝ) ≤ 2 ^ j by positivity)
      have he : (2 : ℝ) ^ j * (1 / 2) ^ j = 1 := by rw [← mul_pow]; norm_num
      rwa [he] at hh
    have hbase : logistic z ^ a * logisticComplement z ^ b * logExp z ^ c ≤ c.factorial := by
      by_cases hc : c = 0
      · simp only [hc, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
        nlinarith [mul_le_mul hqp hwp (by positivity : (0 : ℝ) ≤ logisticComplement z ^ b) (by norm_num : (0 : ℝ) ≤ 1)]
      · have hb := hlog (Nat.pos_of_ne_zero hc)
        have hw : logisticComplement z ^ b ≤ logisticComplement z := by
          simpa using pow_le_pow_of_le_one hw0 hw1 hb
        have hm : logistic z ^ a * logisticComplement z ^ b ≤ logisticComplement z := by
          have h := mul_le_mul_of_nonneg_right hqp (show (0 : ℝ) ≤ logisticComplement z ^ b by positivity)
          nlinarith
        have h := mul_le_mul_of_nonneg_right hm (pow_nonneg (logExp_pos z).le c)
        exact h.trans (by simpa [mul_comm] using logExp_pow_mul_complement_le_factorial z c)
    have h2c : (1 : ℝ) ≤ 2 ^ c := one_le_pow₀ (by norm_num)
    have hbig : (c.factorial : ℝ) ≤ 2 ^ (c + j) * c.factorial * logistic z ^ j := by
      rw [pow_add]
      nlinarith [mul_le_mul_of_nonneg_left hj (show 0 ≤ (2 : ℝ) ^ c * c.factorial by positivity),
        mul_le_mul_of_nonneg_right h2c (show 0 ≤ (c.factorial : ℝ) by positivity)]
    exact hbase.trans hbig

def ProfileJetTerm.bound (t : ProfileJetTerm) (j : ℕ) : ℝ :=
  |t.coeff| * 2 ^ (t.logPower + j) * t.logPower.factorial

lemma ProfileJetTerm.abs_value_le (t : ProfileJetTerm) (j : ℕ)
    (ht : t.admissible j) (z : ℝ) :
    |t.value z| ≤ t.bound j * logistic z ^ j := by
  by_cases hc : t.coeff = 0
  · simp [ProfileJetTerm.value, ProfileJetTerm.bound, hc]
  · obtain ⟨hd, hb⟩ := ht hc
    have h := mul_le_mul_of_nonneg_left
      (profile_jet_monomial_bound z t.qPower t.complementPower t.logPower j hd hb)
      (abs_nonneg t.coeff)
    simpa [ProfileJetTerm.value, ProfileJetTerm.bound, abs_mul,
      abs_of_pos (logistic_pos z), abs_of_pos (logisticComplement_pos z),
      abs_of_pos (logExp_pos z), mul_assoc] using h

def profileJetTerms : ℕ → List ProfileJetTerm
  | 0 => [⟨1, 1, 0, 0⟩]
  | n + 1 => (profileJetTerms n).flatMap (ProfileJetTerm.next (n + 1))

lemma profileJetTerms_admissible (n : ℕ) :
    ∀ t ∈ profileJetTerms n, t.admissible (n + 1) := by
  induction n with
  | zero =>
    intro t ht
    simp only [profileJetTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst t
    simp [ProfileJetTerm.admissible]
  | succ n ih =>
    intro t ht
    obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
    exact s.admissible_next (n + 1) (ih s hs) t ht

def profileJetNumerator (n : ℕ) (z : ℝ) : ℝ :=
  ((profileJetTerms n).map (fun t => t.value z)).sum

def profileJetBound (n : ℕ) : ℝ :=
  ((profileJetTerms n).map (fun t => t.bound (n + 1))).sum

lemma profileJetNumerator_bound (n : ℕ) (z : ℝ) :
    |profileJetNumerator n z| ≤ profileJetBound n * logistic z ^ (n + 1) := by
  unfold profileJetNumerator profileJetBound
  have hgen : ∀ ts : List ProfileJetTerm,
      (∀ t ∈ ts, t.admissible (n + 1)) →
      |(ts.map (fun t => t.value z)).sum| ≤
        (ts.map (fun t => t.bound (n + 1))).sum * logistic z ^ (n + 1) := by
    intro ts
    induction ts with
    | nil => simp
    | cons t ts ih =>
      intro ht
      have hfirst := t.abs_value_le (n + 1) (ht t (by simp)) z
      have hrest := ih (fun s hs => ht s (by simp [hs]))
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add_le _ _).trans (by nlinarith)
  exact hgen _ (profileJetTerms_admissible n)

def ProfileJetTerm.normalizedValue (t : ProfileJetTerm) (j : ℕ) (z : ℝ) : ℝ :=
  t.coeff * logistic z ^ t.qPower * logisticComplement z ^ t.complementPower *
    logExp z ^ ((t.logPower : ℤ) - j)

lemma ProfileJetTerm.normalizedValue_eq_div (t : ProfileJetTerm) (j : ℕ) (z : ℝ) :
    t.normalizedValue j z = t.value z / logExp z ^ j := by
  unfold ProfileJetTerm.normalizedValue ProfileJetTerm.value
  rw [zpow_sub₀ (ne_of_gt (logExp_pos z)), zpow_natCast, zpow_natCast]
  ring

lemma hasDerivAt_pow_of_mul (f : ℝ → ℝ) (x a : ℝ) (n : ℕ)
    (hf : HasDerivAt f (f x * a) x) :
    HasDerivAt (fun y => f y ^ n) ((n : ℝ) * f x ^ n * a) x := by
  cases n with
  | zero => simpa using hasDerivAt_const x (1 : ℝ)
  | succ n =>
    convert! hf.pow (n + 1) using 1
    simp only [Nat.add_sub_cancel, pow_succ]
    ring

lemma ProfileJetTerm.hasDerivAt_normalizedValue (t : ProfileJetTerm) (j : ℕ) (z : ℝ) :
    HasDerivAt (t.normalizedValue j)
      (((t.next j).map (fun s => s.normalizedValue (j + 1) z)).sum) z := by
  have hq := hasDerivAt_pow_of_mul logistic z (logisticComplement z) t.qPower
    (hasDerivAt_logistic z)
  have hw := hasDerivAt_pow_of_mul logisticComplement z (-logistic z) t.complementPower
    (by simpa [mul_comm] using hasDerivAt_logisticComplement z)
  have hL := (hasDerivAt_zpow ((t.logPower : ℤ) - j) (logExp z)
    (Or.inl (ne_of_gt (logExp_pos z)))).comp z (hasDerivAt_logExp z)
  have h := (((hasDerivAt_const z t.coeff).mul hq).mul hw).mul hL
  convert! h using 1
  have h1 : ((t.logPower + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) =
      (t.logPower : ℤ) - j := by omega
  have h2 : (t.logPower : ℤ) - ((j + 1 : ℕ) : ℤ) =
      (t.logPower : ℤ) - j - 1 := by omega
  simp only [ProfileJetTerm.next, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, ProfileJetTerm.normalizedValue, pow_succ, Function.comp_apply,
    Pi.mul_apply, h1, h2, Int.cast_sub, Int.cast_natCast, zero_mul, zero_add]
  ring

def profileJet (n : ℕ) (z : ℝ) : ℝ :=
  ((profileJetTerms n).map (fun t => t.normalizedValue (n + 1) z)).sum

lemma hasDerivAt_profileJet (n : ℕ) (z : ℝ) :
    HasDerivAt (profileJet n) (profileJet (n + 1) z) z := by
  have hgen : ∀ ts : List ProfileJetTerm,
      HasDerivAt (fun x => (ts.map (fun t => t.normalizedValue (n + 1) x)).sum)
        ((ts.flatMap (ProfileJetTerm.next (n + 1))).map
          (fun t => t.normalizedValue (n + 2) z)).sum z := by
    intro ts
    induction ts with
    | nil => simpa using hasDerivAt_const z (0 : ℝ)
    | cons t ts ih =>
      have h := (t.hasDerivAt_normalizedValue (n + 1) z).add ih
      convert! h using 1
      simp only [List.flatMap_cons, List.map_append, List.sum_append]
  exact hgen (profileJetTerms n)

lemma profileJet_eq_div (n : ℕ) (z : ℝ) :
    profileJet n z = profileJetNumerator n z / logExp z ^ (n + 1) := by
  unfold profileJet profileJetNumerator
  simp only [ProfileJetTerm.normalizedValue_eq_div, div_eq_mul_inv, List.sum_map_mul_right]

lemma profileJet_abs_le (n : ℕ) (z : ℝ) :
    |profileJet n z| ≤ profileJetBound n * (logistic z / logExp z) ^ (n + 1) := by
  rw [profileJet_eq_div, abs_div, abs_of_pos (pow_pos (logExp_pos z) _)]
  have h := div_le_div_of_nonneg_right (profileJetNumerator_bound n z)
    (pow_nonneg (logExp_pos z).le (n + 1))
  simpa [div_pow, mul_div_assoc] using h

def logLogExp (z : ℝ) : ℝ := Real.log (logExp z)

lemma contDiff_logLogExp : ContDiff ℝ ∞ logLogExp := by
  have hL : ContDiff ℝ ∞ logExp := by
    apply (contDiff_const.add Real.contDiff_exp).log
    intro z
    positivity
  exact hL.log (fun z => ne_of_gt (logExp_pos z))

lemma hasDerivAt_logLogExp (z : ℝ) :
    HasDerivAt logLogExp (profileJet 0 z) z := by
  have h := (hasDerivAt_logExp z).log (ne_of_gt (logExp_pos z))
  change HasDerivAt (fun y => Real.log (logExp y)) (profileJet 0 z) z
  simpa [profileJet_eq_div, profileJetNumerator, profileJetTerms,
    ProfileJetTerm.value] using h

lemma iteratedDeriv_logLogExp_eq_profileJet (n : ℕ) :
    iteratedDeriv (n + 1) logLogExp = profileJet n := by
  induction n with
  | zero =>
    funext z
    simpa only [Nat.zero_add, iteratedDeriv_one] using (hasDerivAt_logLogExp z).deriv
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (hasDerivAt_profileJet n z).deriv

theorem abs_iteratedDeriv_logLogExp_le (n : ℕ) (z : ℝ) :
    |iteratedDeriv (n + 1) logLogExp z| ≤
      profileJetBound n * (logistic z / logExp z) ^ (n + 1) := by
  rw [iteratedDeriv_logLogExp_eq_profileJet]
  exact profileJet_abs_le n z

lemma log_softplus_eq_log_delta_add_logLogExp (δ t : ℝ) (hδ : 0 < δ) :
    Real.log (softplus δ t) = Real.log δ + logLogExp (t / δ) := by
  unfold softplus logLogExp logExp
  rw [Real.log_mul (ne_of_gt hδ) (ne_of_gt (log_exp_add_one_pos _))]

lemma logSlope_eq_logistic_div_logExp (δ t : ℝ) (hδ : 0 < δ) :
    logSlope δ t = δ⁻¹ * (logistic (t / δ) / logExp (t / δ)) := by
  unfold logSlope logistic logExp
  field_simp [ne_of_gt hδ]

theorem abs_iteratedDeriv_log_softplus_le (n : ℕ) (δ t : ℝ) (hδ : 0 < δ) :
    |iteratedDeriv (n + 1) (fun s => Real.log (softplus δ s)) t| ≤
      profileJetBound n * logSlope δ t ^ (n + 1) := by
  have he : (fun s => Real.log (softplus δ s)) =
      fun s => Real.log δ + logLogExp (δ⁻¹ * s) := by
    funext s
    rw [log_softplus_eq_log_delta_add_logLogExp δ s hδ]
    congr 1
    ring
  rw [he, iteratedDeriv_const_add (by omega),
    iteratedDeriv_comp_const_mul (contDiff_logLogExp.of_le (by simp)) δ⁻¹]
  rw [abs_mul, abs_of_pos (pow_pos (inv_pos.mpr hδ) _)]
  have h := mul_le_mul_of_nonneg_left
    (abs_iteratedDeriv_logLogExp_le n (δ⁻¹ * t))
    (pow_nonneg (inv_pos.mpr hδ).le (n + 1))
  rw [logSlope_eq_logistic_div_logExp δ t hδ, mul_pow]
  have he : δ⁻¹ * t = t / δ := by ring
  rw [he] at h
  convert h using 1 <;> ring

lemma profileJetBound_nonneg (n : ℕ) : 0 ≤ profileJetBound n := by
  unfold profileJetBound
  apply List.sum_nonneg
  intro a ha
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
  unfold ProfileJetTerm.bound
  positivity

theorem exists_uniform_log_softplus_jet_bound (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ t : ℝ, 0 < δ →
      |iteratedDeriv j (fun s => Real.log (softplus δ s)) t| ≤
        C * logSlope δ t ^ j := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n + 1 := ⟨j - 1, by omega⟩
  refine ⟨profileJetBound n + 1, by linarith [profileJetBound_nonneg n], ?_⟩
  intro δ t hδ
  have h := abs_iteratedDeriv_log_softplus_le n δ t hδ
  have hs := pow_nonneg (logSlope_pos δ t hδ).le (n + 1)
  nlinarith

theorem abs_iteratedDeriv_scalar_logProfile_le (n : ℕ) (δ c t : ℝ)
    (p : ℕ) (hδ : 0 < δ) (hp : 1 ≤ p) :
    |iteratedDeriv (n + 1) (fun s => c + (p : ℝ) * Real.log (softplus δ s)) t| ≤
      profileJetBound n * ((p : ℝ) * logSlope δ t) ^ (n + 1) := by
  rw [iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field]
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg p)]
  have h := mul_le_mul_of_nonneg_left (abs_iteratedDeriv_log_softplus_le n δ t hδ)
    (Nat.cast_nonneg p)
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ) ^ (n + 1) :=
    le_self_pow₀ hpR (by omega)
  have hr := mul_le_mul_of_nonneg_right hpPow
    (mul_nonneg (profileJetBound_nonneg n) (pow_nonneg (logSlope_pos δ t hδ).le (n + 1)))
  rw [mul_pow]
  nlinarith

end OAI.AnisotropicCalderon.RadiusProfile
