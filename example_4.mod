# STORM
set TYPES;
set PLACES;
set SCENARIOS;
set ROUTES;

param b{SCENARIOS, PLACES, PLACES};
param f{PLACES, PLACES};
param l{ROUTES};
param pr{SCENARIOS}; # probability
param v{ROUTES, 1..4} symbolic;
param w{ROUTES, PLACES};
param sigma{PLACES}; # maximum landings
param d{TYPES};
param h_max{TYPES};
param h_min{TYPES};
param h{ROUTES, TYPES};
param c{TYPES};
param q;
param p;

param LAS{r in ROUTES} := card({j in PLACES: v[r,j] != 0});
set U{n in PLACES, m in PLACES} := setof{r in ROUTES, j in 1..4, i in 1..4 : v[r,j] == n and v[r,i] == m and j < i} r;
set V1{n in PLACES} := setof{r in ROUTES : n == v[r,1]} r;
set Vl{n in PLACES} := setof{r in ROUTES : n == v[r,LAS[r]]} r;
set W{n in PLACES} := setof{r in ROUTES, j in 1..4 : v[r,j] == n} r; # routes that contain n

var x{ROUTES, TYPES} integer, >= 0;
var y{SCENARIOS, PLACES, PLACES} integer, >= 0;
var d1{SCENARIOS, ROUTES, PLACES, PLACES} integer, >= 0;
var t1{SCENARIOS, ROUTES, PLACES, PLACES, PLACES} integer, >= 0;
var s1{SCENARIOS, ROUTES, PLACES, PLACES} integer, >= 0;
var z1{SCENARIOS, ROUTES, PLACES} integer, >= 0;

check: sum{s in SCENARIOS} pr[s] = 1;

s.t. constr1 {s in SCENARIOS, m in PLACES, n in PLACES}:
   sum{r in ROUTES} (d1[s, r, m, n] + sum{k in PLACES} t1[s, r, m, n, k]) + y[s,m,n] >= b[s,m,n];

s.t. constr2 {s in SCENARIOS, k in PLACES, n in PLACES}:
   sum{r in ROUTES, m in PLACES} t1[s, r, m, k, n] = sum{r in ROUTES} s1[s, r, k, n];

s.t. constr3 {r in ROUTES, s in SCENARIOS}:
   sum{k in PLACES} (d1[s, r, v[r, 1], k] + s1[s, r, v[r, 1], k] + sum{n in PLACES} (t1[s, r, v[r, 1], k, n]))
   = sum{t in TYPES} d[t]*x[r,t] - z1[s,r,v[r, 1]];

s.t. constr4 {r in ROUTES, s in SCENARIOS, j in 2..LAS[r]}:
   sum{k in PLACES} (d1[s, r, v[r, j], k] + s1[s, r, v[r, j], k] + sum{n in PLACES} (t1[s, r, v[r, j], k, n]))
   = z1[s,r,v[r, j - 1]] - z1[s,r,v[r, j]];

s.t. constr5 {m in PLACES, n in PLACES}:
   sum{a in TYPES, r in U[m,n]} x[r,a] >= f[m,n];

s.t. constr6 {a in TYPES, n in PLACES}:
   sum{r in V1[n]} x[r,a] = sum{r in Vl[n]} x[r,a];

s.t. constr7 {n in PLACES}:
   sum{a in TYPES, r in W[n]} x[r,a] <= sigma[n];

s.t. constr8 {a in TYPES}:
   h_min[a] <= sum{r in ROUTES} x[r,a]*h[r,a] <= h_max[a];

minimize overall :
         sum{r in ROUTES, t in TYPES} (c[t]*h[r,t]*x[r,t])
   +     sum{s in SCENARIOS} pr[s] * (q * sum{r in ROUTES, m in PLACES, n in PLACES} (d1[s, r, m, n] + s1[s, r, m, n]
   +     sum{k in PLACES} (t1[s, r, m, n, k]))
   + p * sum{m in PLACES, n in PLACES} (y[s,m,n]));

solve;

printf "\n";
printf "Expected cost with stochastic solution\n";
printf "USD %7.2f\n", overall;
printf "\nRoutes:\n";

for {r in ROUTES} {
  for {a in TYPES} {
    for {{0}: x[r,a] > 0}{
      printf "- route %s, %d flights, served by %s\n", r, x[r,a], a ;
    }
  }
}

printf "\n";

data;

set ROUTES := R1 R2 R3 R4;

# maximum amount of landing at each location
param : PLACES : sigma :=
        1           20
        2           30
        3           10
        4           20
;

# probabilities of distinct scenarios
param : SCENARIOS :   pr :=
        S1          0.33
        S2          0.43
        S3          0.24
;

# aircraft types, operating hour cost, maximum payload, min and max operating hours
param : TYPES :       c   d  h_min  h_max :=
        A320       1180  18      3     35
        B747       1338  23      4     39
        ANT21       988  17      6     32
;

# flying hours required by an aircraft to traverse a route
param h
      : A320 B747  ANT21 :=
    R1     7    7      7
    R2     6    9      6
    R3     8    7      9
    R4     5    5      4
;

# places in routes in visit order, 0 means empty
param v
      :  1  2  3  4 :=
    R1   2  3  2  0
    R2   3  4  3  0
    R3   1  2  1  0
    R4   1  4  1  0 ;

# amount of cargo to be shipped between places in each scenario
param b default 0 :=
 [S1,*,*]:  1  2  3  4 :=
         1  .  2  .  2
         2  .  .  3  4
         3  .  .  .  4
         4  2  1  3  .
 [S2,*,*]:  1  2  3  4 :=
         1  .  1  1  .
         2  1  .  3  4
         3  9  3  .  1
         4  .  4  1  .
 [S3,*,*]:  1  2  3  4 :=
         1  .  1  1  .
         2  .  .  1  1
         3  1  1  .  1
         4  .  1  1  . ;

# minimum number of flights from m to n
param f default 0 :=
      :  1  2  3  4 :=
      1  .  .  .  .
      2  .  .  .  .
      3  .  .  .  .
      4  .  .  .  . ;

param p 300;
param q 400;

end;
