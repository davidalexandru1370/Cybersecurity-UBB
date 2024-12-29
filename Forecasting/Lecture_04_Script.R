library(fpp3)
library(tidyverse)

#lag plots
aus_production
tail(aus_production)


recent_beer <- aus_production |>
  filter(year(Quarter) >= 2000) |>
  select(Quarter, Beer)

recent_beer
recent_beer |> autoplot()

?gg_lag

recent_beer |> gg_lag(lags = 1, geom = "point") +
  scale_color_manual(values = c("black", "red", "brown4", "royalblue")) +
  geom_point(size = 10)
ggsave("Beer_Lag1.png")

recent_beer |> gg_subseries() + geom_point()

recent_beer |> gg_lag(lags = 1) +
  scale_color_manual(values = c("black", "red", "brown4", "royalblue")) +
  geom_point(size = 10)
ggsave("Beer_Lag2.png")


recent_beer |> gg_lag(geom = "point") +
  scale_color_manual(values = c("black", "red", "brown4", "royalblue")) +
  geom_point(size = 4)
ggsave("Beer_Lag3.png")

recent_beer |> gg_lag(lags = c(4, 8, 12, 16, 20), geom = "point") +
  scale_color_manual(values = c("black", "red", "brown4", "royalblue")) +
  geom_point(size = 4)
ggsave("Beer_Lag4.png")

A10 <- PBS |>
  filter(ATC2 == "A10") |>
  select(Month, Concession, Type, Cost) |>
  summarize(TotalCost = sum(Cost)) |>
  mutate(Cost = TotalCost / 1000000)

A10 |> autoplot()
A10 |> gg_lag(lags = 1:24, geom = "point")
ggsave("A10_Lag1.png")


A10 |>
  model(stl = STL(Cost)) |>
  components() |> 
  as_tibble() |>
  mutate(NoTrend = season_year + remainder) |>
  as_tsibble(index = Month) -> A10_NoTrend

A10_NoTrend |> autoplot(NoTrend)

A10_NoTrend |> gg_lag(NoTrend, lags = 1:24, geom = "point")
ggsave("A10_Lag2.png")

A10_NoTrend |> gg_lag(NoTrend, lags = seq(from = 12, to = 203, by = 12), geom = "point") 
ggsave("A10_Lag4.png")

A10_NoTrendL <- A10 |>
  mutate(CostLog = log(Cost)) |>
  model(stl = STL(CostLog)) |>
  components() |>
  mutate(NoTrend = season_year + remainder) |>
  as_tsibble(index = Month) -> A10_NoTrendLog

A10_NoTrendLog |> autoplot(NoTrend)
A10_NoTrendLog |> gg_lag(NoTrend, lags = seq(from = 12, to = 203, by = 12), geom = "point") 
ggsave("A10_Lag3.png")

#ACF
recent_beer |> ACF()
class(recent_beer |> ACF(Beer))
recent_beer |> ACF() |> as_tsibble(index = lag) |> autoplot(acf)
recent_beer |> ACF() |> autoplot()
ggsave("Beer_ACF.png")
recent_beer |> ACF() |> autoplot() + geom_point()


A10 |> ACF() |> autoplot()
A10 |> ACF(lag_max = 40) |> autoplot()
ggsave("A10_ACF.png")
A10 |> ACF(lag_max= 65) |> autoplot()

vic_elec |> ACF(Demand, lag_max = 480) |> autoplot()
ggsave("VicElec_ACF.png")
vic_elec |> ACF(Demand, lag_max = 1000) |> autoplot()


gafa_stock
google <- gafa_stock |> 
  filter(Symbol == "GOOG") |>
  select(Date, Close)
google
google |> tail()
google |> autoplot()

google_2014 <- google |>
  filter(year(Date) == 2014)
google_2014 |> autoplot()

google_2015 <- google |>
  filter(year(Date) == 2015)
google_2015 |> autoplot()


google_2014 |> ACF(lag_max = 100) |> autoplot()
google_2015 |> ACF(lag_max = 100) |> autoplot()
google_2014

?aus_livestock
aus_livestock
aus_livestock |> tail()
aus_livestock$Animal |> unique() |> as_tibble()

aus_livestock |>
  filter(Animal == "Pigs", State == "Victoria", year(Month) >= 2014) -> pigs
pigs
pigs |> autoplot() + geom_point()

pigs |> ACF() |> autoplot()
ggsave("Pigs_ACF.png")

set.seed(39)
wn <- tsibble(sample = 1:100, wn = rnorm(50), index = sample)
wn
wn |> autoplot()
wn |> ACF() |> autoplot()
ggsave("WN_ACF.png")

#stationary
A10 |> autoplot()

aus_production |> autoplot(Gas)
ggsave("AUS_GAS.png")

gafa_stock
google <- gafa_stock |>
  filter(Symbol == "GOOG", year(Date) == 2018)

google |> autoplot(Close)
ggsave("Google_Plot.png")

google |> ACF(Close) |> autoplot()
ggsave("Google_ACF.png")

google |> autoplot(difference(Close))
ggsave("GoogleD_Plot.png")

google |> ACF(difference(Close)) |> autoplot()
ggsave("GoogleD_ACF.png")


google |> features(Close, unitroot_kpss)

library(tseries)
?adf.test
adf.test(google$Close)

google |> features(difference(Close), unitroot_kpss)

google$Close

adf.test(difference(google$Close)[2:251])


pigs |> autoplot()
ggsave("Pigs_Plot.png")
pigs |> ACF() |> autoplot()

pigs |> features(Count, unitroot_kpss)
adf.test(pigs$Count)

lynx |> as_tsibble() |> autoplot()
ggsave("Linx_Plot.png")

lynx |> as_tsibble() |> ACF() |> autoplot()
ggsave("Linx_ACF.png")

lynx |> as_tsibble() |>
  features(value, unitroot_kpss)

lynx |> as_tsibble() -> lynxts
adf.test(lynxts$value)

#Differencing
pigs |> autoplot()

?aus_births

aus_births |> filter(State == "VIC") -> vic_births

vic_births |> autoplot()
ggsave("VicBirths_Plot.png")
vic_births |> ACF() |> autoplot()
ggsave("VicBirths_ACF.png")

vic_births |> features(Births, unitroot_kpss)
adf.test(vic_births$Births)

vic_births |> mutate(BirthDiff = difference(Births)) -> vic_births2
vic_births2
vic_births2 |> autoplot(BirthDiff)
ggsave("VicBirthsD_Plot.png")
vic_births2 |> ACF(BirthDiff) |> autoplot()
ggsave("VicBirthsD_ACF.png")

vic_births2 |> features(BirthDiff, unitroot_kpss)

#adf cannot handle NA in data
vic_births2 |> filter(is.na(BirthDiff) == FALSE) -> vic_births3
vic_births3
adf.test(vic_births3$BirthDiff)

vic_births4 <- vic_births |> mutate(BirthSDiff = difference(Births, 12))
vic_births4 |> head(n = 15)
vic_births4 |> autoplot(BirthSDiff)
ggsave("VicBirthsSD_Plot.png")
vic_births4 |> ACF(BirthSDiff) |> autoplot()
ggsave("VicBirthsSD_ACF.png")

vic_births4 |> features(BirthSDiff, unitroot_kpss)
vic_births5 <- vic_births4 |> filter(is.na(BirthSDiff) == FALSE)
vic_births5
adf.test(vic_births5$BirthSDiff)

beer <- aus_production |> select(Beer)
beer
beer |> autoplot()
beer |> features(Beer, unitroot_kpss)

beerD1 <- beer |> mutate(BeerSD = difference(Beer, 4))
beerD1
beerD1 |> autoplot(BeerSD)

beerD1 |> features(BeerSD, unitroot_kpss)

beerD2 <- beerD1 |> mutate(BeerSDD = difference(BeerSD, 1))
beerD2
beerD2 |> autoplot(BeerSDD)
beerD2 |> features(BeerSDD, unitroot_kpss)

beer |> features(Beer, unitroot_ndiffs)
beer |> features(Beer, unitroot_nsdiffs)
beer |> features(Beer, c(unitroot_ndiffs, unitroot_nsdiffs))


vic_births |> features(Births, c(unitroot_ndiffs, unitroot_nsdiffs))

vic_births |> features(difference(Births, 12), c(unitroot_ndiffs, unitroot_nsdiffs))

vic_births |> features(difference(Births, 1), c(unitroot_ndiffs, unitroot_nsdiffs))

