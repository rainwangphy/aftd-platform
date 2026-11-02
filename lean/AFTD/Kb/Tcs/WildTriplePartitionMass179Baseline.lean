import AFTD.Prelude
import AFTD.Kb.Tcs.WildTriplePartitionLargeOrderMassBound

/-!
# wild_triple_partition_mass_179_baseline

Topic: graphs   Node: ea2bab6aa51f

Provenance: helper lemma. step towards wild_triple_partition_mass_le_of_odd_ge_179

The sum of the canonical triple-partition resource terms wtc_term(179, h) for cut sizes h from 1 to 39 is at most 989/50000 = 0.01978.
-/

/-- Base rational certificate: sum of wtc_term(179, h) for 1 ≤ h < 40 is at most 989/50000. -/
theorem wild_triple_partition_mass_179_baseline :
    ∑ h ∈ Finset.Ico 1 40, wtc_term 179 h ≤ (989 / 50000 : ℝ) := by
  have h1 : wtc_term 179 1 ≤ (6491355141 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 1 = 179 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 1 = 268 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 3 = 25665020 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h2 : wtc_term 179 2 ≤ (12547755994 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 2 = 15931 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 3 = 3172316 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 6 = 32384743329484 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h3 : wtc_term 179 3 ≤ (288315234 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 3 = 939929 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 4 = 210165935 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 9 = 9566123549106398495 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h4 : wtc_term 179 4 ≤ (408704077 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 4 = 41356876 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 6 = 486408039964 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 12 = 1060699432023756750244396 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h5 : wtc_term 179 5 ≤ (14700380 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 5 = 1447490660 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 7 = 18205558067224 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 15 = 55901307835572035561149463960 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h6 : wtc_term 179 6 ≤ (19323549 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 6 = 41977229140 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 9 = 17158738478358620 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 18 = 1614701056049934192472690332739900 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h7 : wtc_term 179 7 ≤ (959102 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 7 = 1037437234460 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 10 = 444411326589488258 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 21 = 28123987656336842484374453441430566570 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h8 : wtc_term 179 8 ≤ (1218383 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 8 = 22304900540890 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 12 = 223235889551837942689 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 24 = 316326218594746837632081766334670619466425 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h9 : wtc_term 179 9 ≤ (77629 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 9 = 423793110276910 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 13 = 4396029825020808717568 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 27 = 2419169481914208135144276180159658964203929856 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h10 : wtc_term 179 10 ≤ (96712 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 10 = 7204482874707470 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 15 = 1355861198888560860175616 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 30 = 13096060777977648572227756487384404853160536160512 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h11 : wtc_term 179 11 ≤ (7560 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 11 = 110687055075051130 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 16 = 21439555207425368601526928 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 33 = 51828056579071684677673167702749811976690881145634320 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h12 : wtc_term 179 12 ≤ (9301 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 12 = 1549618771050715820 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 18 = 4431682176405455603868566176 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 36 = 153963473583000880132006363340594635564544795700700465952 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h13 : wtc_term 179 13 ≤ (865 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 13 = 19906641135805349380 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 19 = 58311607584282310577217976000 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 39 = 350974891784993225299280180442657095018607382102157564536000 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h14 : wtc_term 179 14 ≤ (1055 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 14 = 236035887753120571220 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 21 = 8573472360820479149438962985600 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 42 = 625533133228857730510716109305423669163748803751887320606147200 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h15 : wtc_term 179 15 ≤ (115 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 15 = 2596394765284326283420 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 22 = 96256712414666288632337448065600 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 45 = 885718548446642263976981527281752856020219250949663615320129659200 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h16 : wtc_term 179 16 ≤ (139 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 16 = 26613046344164344405055 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 24 = 10509768219623074666432931150206000 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 48 = 1010279376549709083475844289037626469105699182819745876226256912926000 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h17 : wtc_term 179 17 ≤ (18 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 17 = 255172150241105184589645 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 25 = 102575337823521208744385408026010560 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 51 = 939642971156483046737893056613463708309983177280435839893148907621360320 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h18 : wtc_term 179 18 ≤ (21 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 18 = 2296549352169946661306805 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 27 = 8592657145370353563279669949255807680 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 54 = 720299753063663089086094755074383250362180355338637729139571832792214475200 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h19 : wtc_term 179 19 ≤ (3 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 19 = 19460233984176916445810295 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 28 = 73958227572651971741085730634666058960 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 57 = 459438027876204891351395065159924487464207920176515587701083982743886307687120 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h20 : wtc_term 179 20 ≤ (4 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 20 = 155681871873415331566482360 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 30 = 4876142452376226550653652309430396714880 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 60 = 245923669757081529710340425269775874924091113546359700739253280787856684466764160 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h21 : wtc_term 179 21 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 21 = 1178734172755858939003366440 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 31 = 37436190440823932872760298375626916714240 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 63 = 111315899063233175756512896356247837197924795684826327788346824796597529915032672000 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h22 : wtc_term 179 22 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 22 = 8465454513428441471024177160 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 33 = 1982841859598640353635633531009057486421280 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 66 = 42904358534519966893553046589246654374460925626038359796776607050400897573385756192800 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h23 : wtc_term 179 23 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 23 = 57785928635141970041338948440 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 34 = 13704936382520014208952172934915544391441200 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 69 = 14169685622657032288700099203800239375984847770855239121374054245360342470320297088406000 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h24 : wtc_term 179 24 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 24 = 375608536128422805268703164860 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 36 = 593032175752187471984516168855131199452505640 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 72 = 4032923462722363465745413365803058754049041150971606139329138594445624732192008853988951400 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h25 : wtc_term 179 25 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 25 = 2328772923996221392665959622132 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 37 = 3718472020932634959470479761470011845215711040 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 75 = 994388427014094573501058051472354100916170746572065708769162627848212366769880897064968034880 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h26 : wtc_term 179 26 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 26 = 13793501165208388248867606992628 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 39 = 133307974677564706745389061893995768782935713600 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 78 = 213431184041102120705095516594359727368707660443392969839664602086530277831195286469227855745600 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h27 : wtc_term 179 27 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 27 = 78163173269514200076916439624892 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 40 = 763188155029057946117352379343125776282306960360 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 81 = 40054391662311057389088200281491770603522696983386168358092524603032500402927992125811154787431720 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h28 : wtc_term 179 28 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 28 = 424314369177362800417546386535128 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 42 = 22938191725716563913617706007713599115718396655280 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 84 = 6599499518407636428882710260308439864733805751282630248809549697230177094010489540117853769546015600 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h29 : wtc_term 179 29 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 29 = 2209361025716613202174120840234632 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 43 = 120558868139812638243665152505657520933775759164960 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 87 = 958269246425734509629653927306211654225025148693714222196938407740198477315921380129005206476973678880 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h30 : wtc_term 179 30 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 30 = 11046805128583066010870604201173160 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 45 = 3068771189013412609838749336507645987405201142380800 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 90 = 123057823963884925996568020164389100274943985386898623099692642105309246749905654657628738057492472838400 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h31 : wtc_term 179 31 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 31 = 53095934327705704374829678257251640 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 46 = 14876869024999804608566110913939240330246953364150400 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 93 = 14021660766282092181766754732911237939844226469880121485068522583409630427714549715276099944123688529936000 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h32 : wtc_term 179 32 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 32 = 245568696265638882733587261939788835 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 48 = 323532335152721814585758215274683957926673770368770800 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 96 = 1421954596809873455270041763124292562623434049579645037761717580064150693373121213568393406346389549031746800 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h33 : wtc_term 179 33 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 33 = 1093896919728755023085979621368150265 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 49 = 1452594157828546922629934844090417770283025091451624000 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 99 = 128708879999904009662587285363209161853956195415559623005648251061476732864082518094128805234240208664935432000 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h34 : wtc_term 179 34 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 34 = 4697322067070536275604500727051468785 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 51 = 27195980503157053796156215422182245172098895653366052160 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 102 = 10426270842529673186600709888189147733978641078735996765331325554460720997218020003717356522300458048493685930560 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h35 : wtc_term 179 35 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 35 = 19460334277863650284647217297784656395 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 52 = 113490918638174628341651898973337446198951160707316025360 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 105 = 757767582535287209172609883503682780239481642419030106954859802951505130773724233156655007723363032704068640987920 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h36 : wtc_term 179 36 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 36 = 77841337111454601138588869191138625580 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 54 = 1841550755260946799506049681454154787379207513363995883200 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 108 = 49528148852500362714145579160549296301104966598313824624208840515253904385926401738995899340987787286561467548683200 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h37 : wtc_term 179 37 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 37 = 300846248836162377373465089036022255620 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 55 = 7165306575015320274441720578748893172711825597452638527360 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 111 = 2917688143613643236955692116187689400755308965617127134373539329126572108837261373438015113798669295647328497973045120 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h38 : wtc_term 179 38 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 38 = 1124214929861448883869264280081977902580 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 57 = 101364844517979887942572159916661973717724059109828115708480 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 114 = 155239394034124335876715500336551565852450154567414032797433033155529263735468467063845951863742326096093595169200936000 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  have h39 : wtc_term 179 39 ≤ (1 / 1000000000000 : ℝ) := by
    have c179 : Nat.choose 179 39 = 4064469361806776733988878551065612417020 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c268 : Nat.choose 268 58 = 368758313677478557860046995558890973352409939175409179560160 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have c537 : Nat.choose 537 117 = 7474724008049002968197810940936708232882400933891868637171633803566192379928656114567864009345870658099160848418158831200 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    unfold wtc_term
    norm_num only [Nat.reduceMul, Nat.reduceDiv]
    rw [c179, c268, c537]
    norm_num
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num only [Nat.reduceSub, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, zero_add]
  linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39]
