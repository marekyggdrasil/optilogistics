
set CARRIERS;
set OFFERS;
set OPTIONS;
set PARCELS;
set WEIGHTS;
set DISCOUNTS;

param PROMO2016  symbolic, in CARRIERS;
param PROMO2016D symbolic, in DISCOUNTS;
param PROMO2016R symbolic, in WEIGHTS;

param PENALTY1 symbolic, in CARRIERS;
param PENALTY1VALUE;

param weight{PARCELS};
param max_weight{WEIGHTS};
param min_weight{WEIGHTS};
param base_rate{WEIGHTS, CARRIERS};
param extra_charge{CARRIERS, WEIGHTS, OFFERS};
param delivery_time{CARRIERS, OFFERS};
param discounts{CARRIERS, DISCOUNTS, WEIGHTS};

var d{PARCELS, CARRIERS, DISCOUNTS, WEIGHTS} binary; # if discount applies or not
var wx{PARCELS, WEIGHTS, CARRIERS} binary; # if we apply a carrier to parcel
var e1 binary;
var final_rate{PARCELS} >= 0;
var final_extra{PARCELS} >= 0;
var final_discount{PARCELS} >= 0;
var final_extra_general >= 0;

# for every parcel only one carier selected
s.t. rtk {p in PARCELS}: sum{c in CARRIERS, we in WEIGHTS} wx[p,we,c] = 1;

# for every parcel only one option selected

# weight constraint
s.t. rtw {p in PARCELS}: weight[p] <= sum{ca in CARRIERS, we in WEIGHTS} wx[p, we, ca]*max_weight[we];
#s.t. rtu {p in PARCELS}: weight[p] >= sum{ca in CARRIERS, we in WEIGHTS} wx[p, we, ca]*min_weight[we]; # comment this one for example

s.t. rti {p in PARCELS}: sum{ca in CARRIERS, we in WEIGHTS} wx[p, we, ca] = 1;

# bind variables of weight and carier together
#s.t. rtr {p in PARCELS}: sum{ca in CARRIERS, we in WEIGHTS} wx[p, we, ca] = sum{ca in CARRIERS, we in WEIGHTS} wx[p, we, ca];

# rate must be affected by selected carrier and by weight TODO linearize this thing
s.t. rtc {p in PARCELS}: final_rate[p] = sum{c in CARRIERS, we in WEIGHTS} wx[p, we, c] * base_rate[we, c];

# discount constraints
s.t. rto {p in PARCELS, we in WEIGHTS, ca in CARRIERS}: sum{di in DISCOUNTS} d[p, ca, di, we] <= wx[p, we, ca];
s.t. rtv {p in PARCELS, di in DISCOUNTS}: sum{we in WEIGHTS, ca in CARRIERS} d[p, ca, di, we] <= 1;
s.t. rtd {p in PARCELS}: final_discount[p] = sum{di in DISCOUNTS, c in CARRIERS, we in WEIGHTS} d[p, c, di, we] * discounts[c, di, we];

# extra charges parcel specific

# common extra charges
s.t. extr : final_extra_general = e1 * PENALTY1VALUE;

# specific logic constraints

# C1 gives discount D1 on all the C1 parcels if and only if there are more than two parcels that weight more than 0.5kg are sent
s.t. special1 {p in PARCELS}: sum{we in WEIGHTS} 2 * d[p, PROMO2016, PROMO2016D, we] <= sum{pa in PARCELS} wx[pa, PROMO2016R, PROMO2016];

# C2 charges extra if only one parcel is being sent
#s.t. special2 : sum{we in WEIGHTS} 3 * e1 <= sum{pa in PARCELS, we in WEIGHTS} wx[pa, we, PENALTY1];

minimize overall : final_extra_general + sum{p in PARCELS} (final_rate[p] - final_discount[p]);

solve;

printf "\nSolution:\n\n";
for {p in PARCELS} {
	for {c in CARRIERS} {
		for {we in WEIGHTS} {
			# GLPK has no IF ... THEN ... ELSE for expressions
			for {{0}: wx[p,we,c]}{
				printf "parcel %2s (%2s) carrier %2s %10.1f %10.1f\n", p, we, c, final_rate[p], final_discount[p];
			}
		}
	}
}
printf "\nTotal price: %f\n\n", overall;

printf "\nWeight options:\n";
for {p in PARCELS} {
	for {c in CARRIERS} {
		for {we in WEIGHTS} {
			# GLPK has no IF ... THEN ... ELSE for expressions
			for {{0}: wx[p,we,c]}{
				printf "- parcel %2s weight class %2s: %f kg\n", p, we, weight[p];
			}
		}
	}
}
printf "\n";

printf "\nDiscounts:\n";
for {p in PARCELS} {
	printf "\n- parcel %2s: ", p;
	for {c in CARRIERS} {
		for {we in WEIGHTS} {
			for {di in DISCOUNTS} {
				# GLPK has no IF ... THEN ... ELSE for expressions
				for {{0}: d[p, c, di, we]}{
					printf "%2s, ", di;
				}
			}
		}
	}
}
printf "\n\n";

data;

set CARRIERS  := C1 C2 C3 C4;
set DISCOUNTS := D1 D2 D3;

param : PARCELS :     weight :=
        P1              0.31
        P2              0.21
        P3              0.35
        P4              0.5
        P5              0.35
;

param : WEIGHTS :    max_weight    min_weight:=
        KG01                0.1            0.0
        KG02                0.4            0.1
        KG03                0.3            0.2
        KG04                0.4            0.3
        KG05                0.5            0.4
;

param base_rate
      : C1 C2 C3 C4  :=
   KG01 1  1  2  8
   KG02 2  2  2  7
   KG03 2  2  2  6
   KG04 2  3  2  6
   KG05 3  3  3  6 ;

param delivery_time default 99999999
     :  C1 C2 C3 C4  :=
   OFF1 3  .  3  3
   OFF2 3  3  .  3
   OFF3 .  3  .  .
   OFF4 .  .  3  .
   OFF5 3  .  3  3 ;

param extra_charge default 0 :=
   [C2, KG04, OFF1] 0.1
   [C2, KG05, OFF1] 0.1
   [C2, KG05, OFF2] 0.1 ;

param discounts default 0 :=
 [C1,*,*]: KG01 KG02 KG03 KG04 KG05 :=
       D1  1    1    1    1    1
       D2  .    .    .    .    .
       D3  .    .    .    .    .
 [C2,*,*]: KG01 KG02 KG03 KG04 KG05 :=
       D1  .    .    .    .    .
       D2  .    .    .    .    .
       D3  .    .    .    .    .
 [C3,*,*]: KG01 KG02 KG03 KG04 KG05 :=
       D1  .    .    .    .    .
       D2  .    .    .    .    .
       D3  .    .    .    .    .
 [C4,*,*]: KG01 KG02 KG03 KG04 KG05 :=
       D1  .    .    .    .    .
       D2  .    .    .    .    .
       D3  .    .    .    .    . ;

param PROMO2016 C1;
param PROMO2016D D1;
param PROMO2016R KG05;

param PENALTY1 C2;
param PENALTY1VALUE := 2;

end;
