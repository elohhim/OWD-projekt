###########################################################
# System wspomagajacy decyzje w zakresie planowania pracy #
# ujec wody.                                              #
# MODEL                                                   #
# Autor: Jan Kumor                                        #
###########################################################

##########
# Zbiory #
##########

# Ujecia wody
set INTAKES;

# Zakresy wolumenu produkcji ujec o roznych kosztach
set RANGES ordered;

#############
# Parametry #
#############

# Liczba godzin
param T >= 1;

# Maksymalna wydajnoœc ujec wody [t/h]
param efficiency {INTAKES} >= 0;

# Koszta zmienne pracy ujec [zl/t] 
param variableCost {INTAKES, RANGES} >= 0;

# Progi zakresow wolumenu produkcji o roznych kosztach [t/h]
param threshold {INTAKES, RANGES} >= 0;

# Koszta stale pracy ujec [zl/h]
param fixedCost {INTAKES} >= 0;

# Iloœc wytwarzanych zanieczyszczeñ [g/t]
param pollution {INTAKES} >= 0;

# Zapotrzebowanie na wode w kolejnych godzinach [t]
param hourlyDemand {1..T} >= 0;

###########
# Zmienne #
###########

# Aktywnoœc danego ujecia w danej godzinie
var active {1..T, INTAKES} binary;
# Wolumen produkcji wody danego ujecia w danej godzinie
var intakeProduction {1..T, i in INTAKES} >=0, <= efficiency[i];
# Godzinowa produkcja
var hourlyProduction {1..T} >= 0;
# Wolumen produkcji wody przypadajacy na dany zakres kosztow dla danego ujecia w danej godzinie
var intakeProductionInRange {1..T, i in INTAKES, r in RANGES} >=0; 
var thresholdExceeded {t in 1..T, i in INTAKES, r in RANGES} binary;
# Koszt zmienny poboru wody przez dane ujecie w danej godzinie
var intakeVariableCost {1..T, INTAKES} >= 0; 
# Koszta stale pracy ujec dla danej godziny
var hourlyFixedCost {1..T} >= 0;
# Koszta zmienne pracy ujec w danej godzinie
var hourlyVariableCost {1..T} >= 0;
# Koszt pracy ujec dla danej godziny
var hourlyCost {1..T} >= 0;
# Calkowity koszt pracy ujec wody
var totalCost >= 0;
# Calkowita iloœc wytwarzanych zanieczyszczeñ przy zalozonym wolumenie produkcji
var totalPollution >= 0;

#######################
# Ograniczenia modelu #
#######################
# Obliczenie godzinowej produkcji
subject to CalculateHourlyProduction {t in 1..T}:
	hourlyProduction[t] = sum {i in INTAKES} intakeProduction[t,i];
# Ograniczenia zakresow kosztow produkcji
subject to Range1 {t in 1..T, i in INTAKES}:
	intakeProductionInRange[t,i,first(RANGES)] <= threshold[i,first(RANGES)];
subject to Range2 {t in 1..T, i in INTAKES, r in RANGES: r != first(RANGES)}:
	intakeProductionInRange[t,i,r] <= (threshold[i,r]-threshold[i,prev(r)]) * thresholdExceeded[t,i,prev(r)];
subject to Range3 {t in 1..T, i in INTAKES}:
	threshold[i,first(RANGES)]*thresholdExceeded[t,i,first(RANGES)] <= intakeProductionInRange[t,i,first(RANGES)];
subject to Range4 {t in 1..T, i in INTAKES, r in RANGES: r != first(RANGES)}:
	(threshold[i,r]-threshold[i,prev(r)])*thresholdExceeded[t,i,r] <= intakeProductionInRange[t,i,r];
# Obliczenie wolumenu produkcji dla danego ujecia
subject to CalculateIntakeProduction {t in 1..T, i in INTAKES}:
	intakeProduction [t,i] = sum {r in RANGES} intakeProductionInRange[t,i,r];
# Obliczenie kosztow pracy ujec
subject to CalculateHourlyFixedCost {t in 1..T}:
	hourlyFixedCost[t] = sum {i in INTAKES} fixedCost[i] * active[t,i];
subject to CalculateIntakeVariableCost {t in 1..T, i in INTAKES}:
	intakeVariableCost[t,i] = sum {r in RANGES} intakeProductionInRange[t,i,r]*variableCost[i,r];
subject to CalculateHourlyVariableCost {t in 1..T}:
	hourlyVariableCost[t] = sum {i in INTAKES} intakeVariableCost[t,i];
subject to CalculateHourlyCost {t in 1..T}:
	hourlyCost[t] = hourlyFixedCost[t] + hourlyVariableCost[t];
subject to CalculateTotalCost:
	totalCost = sum {t in 1..T} hourlyCost[t];
# Obliczenie calkowitej liczby wyprodukowanych zanieczyszczeñ
subject to CalculateTotalPollution:
	totalPollution = sum {t in 1..T, i in INTAKES} intakeProduction[t,i] * pollution[i];
# Ograniczenia wolumenu planowanej produkcji aktywnych ujec
subject to InactiveIntakesProduction {t in 1..T, i in INTAKES}:
	active[t,i] = 0 ==> intakeProduction[t,i] = 0;
# Zapewnienie aktywnoœci co najmniej dwoch ujec w kazdej godzinie
subject to NumberOfActive {t in 1..T}:
	sum {i in INTAKES} active[t,i] >= 2;
# Pokrycie zapotrzebowania na wode w kazdej godzinie
subject to HourlyDemand {t in 1..T}:
	hourlyProduction[t] = hourlyDemand[t];

#############################
# Metoda punktu odniesienia #
#############################
# Skladniki wektora oceny
set RATED = {"COST", "PLTN"};
# Wektor oceny
var value {r in RATED} = 
	if r == "COST" then totalCost
 	else if r == "PLTN" then totalPollution;
# Wektor aspiracji
param aspiration {RATED};
# Wspolczynniki normalizujace - ujemna lambda gdy minimalizujemy skladnik
param lambda {RATED};
# Wspolczynnik skladnika regularyzacyjnego
param epsilon;
# Wspolczynnik pomniejszenia wartoœci ocen ponad poziomem aspiracji
param beta;
# Indywidualne funkcje osiagniec
var individualRating {RATED};
# Zmienna pomocnicza metody punktu odniesienia
var v;
# Skalaryzujaca funkcja osiagniecia
var rating = v + epsilon * (sum {r in RATED} individualRating[r]);
# Odlegloœc od punktu odniesienia
var distance {r in RATED} = value[r]-aspiration[r];
# Znormalizowana odlegloœc od punktu odniesienia
var normalizedDistance {r in RATED} = lambda[r]*distance[r];

# Ograniczenia zmiennej v przez indywidualne funkcje osiagniec
subject to VSubject {r in RATED}:
	v <= individualRating[r]; 
# Ograniczenia indywidualnych funkcji osiagniec
subject to IndividualRatingSubjectBeta {r in RATED}:
	individualRating[r] <= beta*normalizedDistance[r];
subject to IndividualRatingSubject {r in RATED}:
	individualRating[r] <= normalizedDistance[r];
	
################
# Funkcje celu #
################
maximize MaximizeRating: rating;
minimize MinimizeCost: totalCost;
minimize MinimizePollution: totalPollution;
maximize MaximizeCost: totalCost;
maximize MaximizePollution: totalPollution