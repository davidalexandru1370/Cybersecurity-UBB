library(fpp3)
library(tidyverse)
library(lubridate) #for days_in_month
library(cowplot) #for plot_grid

google_2018 <- gafa_stock |> 
  filter(Symbol == "GOOG", year(Date) == 2018) |>
  select(Date, Close)

google_2018

google_2018 |> autoplot() + geom_point()
google_2018 |> ACF() |> 
  autoplot() + geom_point()

google_2018 |> features(Close, unitroot_kpss)


google_2018 |> autoplot(difference(Close)) + geom_point() 
google_2018 |> features(difference(Close), unitroot_kpss)

google_2018 |> ACF(difference(Close)) |> 
  autoplot() + geom_point()

#first value after difference is NA. max, min, mean cannot handle it
diff <- difference(google_2018$Close) |> tail(250)
diff
max(diff)
min(diff)
mean(diff)

google_2018 |> ggplot() + 
  geom_density(mapping = aes(x = difference(Close)))

data()

A10 <- PBS |>
  filter(ATC2 == "A10") |>
  select(Month, Concession, Type, Cost) |>
  summarize(TotalCost = sum(Cost)) |>
  mutate(Cost = TotalCost / 1000000)

A10 |> autoplot() + geom_point()
A10 |> head(n = 10)

A10_oneYear = A10 |> head(n= 10)



p1 <- A10_oneYear |> autoplot() + geom_point()
p1
A10_oneYear |> 
  mutate(CostPerDay = Cost / days_in_month(Month)) -> A10_oneYear
p2 <- A10_oneYear |> autoplot(CostPerDay) + geom_point()
p2


plot_grid(p1, p2)
ggsave("CostPerDay.png")

global_economy |>
  filter(Country == "Romania") -> ro_economy

ro_economy
p1 <- ro_economy |> autoplot(GDP) +  geom_point()
p1

ro_economy |>
  filter(is.na(GDP) == FALSE, is.na(Population) == FALSE) -> ro_economy
ro_economy
ro_economy |> autoplot(GDP) +  geom_point()

ro_economy |>
  mutate(GDPPerCapita = GDP / Population) -> ro_economy

p2 <- ro_economy |> autoplot(GDPPerCapita) + geom_point()
p2

plot_grid(p1, p2) 
ggsave("GDPPerCapitaRo.png")

#inflation
#CPI
global_economy |> 
  filter(Country == "Romania") 

#Retail Turnover
aus_retail |> view()
aus_retail

aus_retail |> distinct(Industry)

book_retail <- aus_retail |>
  filter(Industry == "Newspaper and book retailing")
book_retail
book_retail |> distinct(State)

book_retail |>
  group_by(Industry) |>
  index_by(Year = year(Month)) |>
  summarise(Turnover = sum(Turnover)) -> book_retail_year

book_retail_year |> view()

book_retail_year |> autoplot(Turnover) + geom_point()
ggsave("NewsPaper.png")

aus_economy <- global_economy |>
  filter(Country == "Australia")
aus_economy |> autoplot(CPI) + geom_point()

aus_economy |> tail()
book_retail_year |> tail()

book_retail_CPI <- book_retail_year |>
  left_join(aus_economy, by = "Year")

book_retail_CPI
book_retail_CPI |> view()

book_retail_CPI <- book_retail_CPI |>
  mutate(Adjusted_turnover = Turnover / CPI * 100) |>
  select(Year, Industry, Turnover, Adjusted_turnover)

book_retail_CPI
p1 <- book_retail_CPI |> autoplot(Adjusted_turnover) + geom_point()
p1
p2 <- book_retail_CPI |> autoplot(Turnover) + geom_point()
p2

plot_grid(p1, p2, nrows = 2, ncol = 1)
ggsave("TurnoverPair.png")

#Mathematical transformations
food_retail <- aus_retail |>
  filter(Industry == "Food retailing") |>
  summarize(Turnover = sum(Turnover))

food_retail |> autoplot() + geom_point()
ggsave("Foodretail.png")


food_retail |> autoplot(sqrt(Turnover)) + geom_point()
ggsave("FoodIndustry_SQRT.png")

food_retail |> autoplot(Turnover^(1/3)) + geom_point() 
ggsave("Food_Industry_CubeRoot.png")

food_retail |> autoplot(log(Turnover)) + geom_point()
ggsave("FoodIndustry_Log.png")

food_retail |> autoplot(-1 / Turnover) + geom_point()
ggsave("Food_industry_Inverse.png")


#Box cox
food_retail |> autoplot(Turnover) + geom_point()
ggsave("T01.png")
food_retail |> autoplot(box_cox(Turnover, 1)) + geom_point()
ggsave("T02.png")
food_retail |> autoplot(box_cox(Turnover, 0.95)) + geom_point()
ggsave("T03.png")
food_retail |> autoplot(box_cox(Turnover, 0.9)) + geom_point()
ggsave("T04.png")
food_retail |> autoplot(box_cox(Turnover, 0.85)) + geom_point()
ggsave("T05.png")
food_retail |> autoplot(box_cox(Turnover, 0.8)) + geom_point()
ggsave("T06.png")
food_retail |> autoplot(box_cox(Turnover, 0.75)) + geom_point()
ggsave("T07.png")
food_retail |> autoplot(box_cox(Turnover, 0.7)) + geom_point()
ggsave("T08.png")
food_retail |> autoplot(box_cox(Turnover, 0.65)) + geom_point()
ggsave("T09.png")
food_retail |> autoplot(box_cox(Turnover, 0.6)) + geom_point()
ggsave("T10.png")
food_retail |> autoplot(box_cox(Turnover, 0.55)) + geom_point()
ggsave("T11.png")
food_retail |> autoplot(box_cox(Turnover, 0.5)) + geom_point()
ggsave("T12.png")
food_retail |> autoplot(box_cox(Turnover, 0.45)) + geom_point()
ggsave("T13.png")
food_retail |> autoplot(box_cox(Turnover, 0.4)) + geom_point()
ggsave("T14.png")
food_retail |> autoplot(box_cox(Turnover, 0.35)) + geom_point()
ggsave("T15.png")
food_retail |> autoplot(box_cox(Turnover, 0.3)) + geom_point()
ggsave("T16.png")
food_retail |> autoplot(box_cox(Turnover, 0.25)) + geom_point()
ggsave("T17.png")
food_retail |> autoplot(box_cox(Turnover, 0.2)) + geom_point()
ggsave("T18.png")
food_retail |> autoplot(box_cox(Turnover, 0.15)) + geom_point()
ggsave("T19.png")
food_retail |> autoplot(box_cox(Turnover, 0.10)) + geom_point()
ggsave("T20.png")
food_retail |> autoplot(box_cox(Turnover, 0.05)) + geom_point()
ggsave("T21.png")
food_retail |> autoplot(box_cox(Turnover, 0)) + geom_point()
ggsave("T22.png")
food_retail |> autoplot(box_cox(Turnover, -0.1)) + geom_point()
ggsave("T23.png")
food_retail |> autoplot(box_cox(Turnover, -0.2)) + geom_point()
ggsave("T24.png")
food_retail |> autoplot(box_cox(Turnover, -0.3)) + geom_point()
ggsave("T25.png")
food_retail |> autoplot(box_cox(Turnover, -0.4)) + geom_point()
ggsave("T26.png")
food_retail |> autoplot(box_cox(Turnover, -0.5)) + geom_point()
ggsave("T27.png")
food_retail |> autoplot(box_cox(Turnover, -0.6)) + geom_point()
ggsave("T28.png")
food_retail |> autoplot(box_cox(Turnover, -0.7)) + geom_point()
ggsave("T29.png")
food_retail |> autoplot(box_cox(Turnover, -0.8)) + geom_point()
ggsave("T30.png")
food_retail |> autoplot(box_cox(Turnover, -0.9)) + geom_point()
ggsave("T31.png")
food_retail |> autoplot(box_cox(Turnover, -1)) + geom_point()
ggsave("T32.png")


food_retail |> features(Turnover, guerrero)

food_retail |> autoplot(box_cox(Turnover, 0.0895)) + geom_point()

#Decomposition example
?us_employment
us_retail_employment <- us_employment |>
  filter(Year(Month) >= 1990, Title = "Retail Trade") |>
  select(-Series_ID)

us_retail_employment
us_retail_employment |> autoplot() + geom_point()
ggsave("USEmployed.png")

dcmp <- us_retail_employment |>
  model(stl = STL(Employed))

dcmp
components(dcmp) |> print(n = 15)

components(dcmp) |> autoplot()
ggsave("Employment_Components.png")

us_retail_employment |>
  autoplot(Employed, color = "gray", size = 3) +
  autolayer(components(dcmp), trend, color = "red", size = 2) 
ggsave("Employment_trend.png")

components(dcmp) |> gg_subseries(season_year)
ggsave("Employment_season_subseries.png")

us_retail_employment |>
  autoplot(Employed, color = "gray", size = 3) +
  autolayer(components(dcmp), season_adjust, color = "red", size= 2) 
ggsave("Employment_seasonallyadjusted.png")

#beer production

beer <- aus_production |> select(Quarter, Beer)
beer |> autoplot() + geom_point()
ggsave("Plot_Beer.png")

dcmpBeer <- beer |> model(stl = STL(Beer))
components(dcmpBeer)
components(dcmpBeer) |> autoplot()
ggsave("Decompose_Beer.png")


A10 |> autoplot() + geom_point()

dcmpA10 <- A10 |> model(stl = STL(TotalCost))
components(dcmpA10)
components(dcmpA10) |> autoplot()
ggsave("Decompose_A10.png")


dcmpA10L <- A10 |> model(stl = STL(log(TotalCost)))
components(dcmpA10L)
components(dcmpA10L) |> autoplot()
ggsave("Decompose_A10Log.png")


#white noise
components(dcmp) |>
  ACF(remainder, lag_max = 30) |>
  autoplot() + geom_point()
ggsave("Employment_Decompose_ACF.png")

us_retail_employment |> ACF(Employed, lag_max = 30) |> autoplot()

components(dcmpBeer) |>
  ACF(remainder, lag_max = 30) |>
  autoplot() + geom_point()

components(dcmpA10) |>
  ACF(remainder, lag_max = 30) |>
  autoplot() + geom_point()

vic_elec |> autoplot(Demand)
ggsave("Plot_VicElec.png")

dcmpVicElec <- vic_elec |>
  model(stl = STL(Demand))
dcmpVicElec |> components()

dcmpVicElec |> components() |> autoplot()
ggsave("Vic_Elec_Decomposed.png")


vic_elec_short <- vic_elec |> head(n = 1000)
vic_elec_short|> autoplot(Demand)

dcmpVicElec2 <- vic_elec_short |>
  model(stl = STL(Demand))
dcmpVicElec2 |> components()

dcmpVicElec2 |> components() |> autoplot()
ggsave("Vic_Elec_short_Decomposed.png")

google <- gafa_stock |> 
  filter(Symbol == "GOOG")
google |> autoplot(Close)
google

dcmpGoogle <- google |>
  model(stl = STL(Close))

google <- google |>
  mutate(TS = seq(from = 1, to = 1258, by = 1))
google

google <- tsibble(Close = google$Close, TS = google$TS, index = TS)

dcmpGoogle <- google |> model(stl = STL(Close))
dcmpGoogle |> components()
dcmpGoogle |> components() |> autoplot()
ggsave("Google_Decompose.png")


#moving average
global_economy |> filter(Country == "Australia") |> select(Exports) -> aus_exports
aus_exports |> autoplot() + geom_point()
ggsave("AusExports.png")

aus_exports_withMA <- aus_exports |>
  mutate(MA3 = slider::slide_dbl(Exports, mean, .before=1, .after = 1, .complete = TRUE)) |>
  mutate(MA5 = slider::slide_dbl(Exports, mean, .before=2, .after = 2, .complete = TRUE)) |>
  mutate(MA7 = slider::slide_dbl(Exports, mean, .before=3, .after = 3, .complete = TRUE)) |>
  mutate(MA9 = slider::slide_dbl(Exports, mean, .before=4, .after = 4, .complete = TRUE)) |>
  mutate(MA11 = slider::slide_dbl(Exports, mean, .before=5, .after = 5, .complete = TRUE)) |>
  mutate(MA13= slider::slide_dbl(Exports, mean, .before=6, .after = 6, .complete = TRUE)) |>
  mutate(MA15 = slider::slide_dbl(Exports, mean, .before=7, .after = 7, .complete = TRUE)) |>
  mutate(MA17 = slider::slide_dbl(Exports, mean, .before=8, .after = 8, .complete = TRUE)) 

aus_exports_withMA |> autoplot(Exports, color = "grey", size = 3) +
  autolayer(aus_exports_withMA, MA3, color = "red", size = 2)
ggsave("AusExportsMA3.png")

aus_exports_withMA |> autoplot(Exports, color = "grey", size = 3) +
  autolayer(aus_exports_withMA, MA5, color = "red", size = 2)
ggsave("AusExportsMA5.png")

aus_exports_withMA |> autoplot(Exports, color = "grey", size = 3) +
  autolayer(aus_exports_withMA, MA7, color = "red", size = 2)
ggsave("AusExportsMA7.png")

aus_exports_withMA |> autoplot(Exports, color = "grey", size = 3) +
  autolayer(aus_exports_withMA, MA9, color = "red", size = 2)
ggsave("AusExportsMA9.png")

aus_exports_withMA |> autoplot(Exports, color = "grey", size = 3) +
  autolayer(aus_exports_withMA, MA11, color = "red", size = 2)
ggsave("AusExportsMA11.png")

aus_exports_withMA |> autoplot(Exports, color = "grey", size = 3) +
  autolayer(aus_exports_withMA, MA13, color = "red", size = 2)
ggsave("AusExportsMA13.png")

aus_exports_withMA |> autoplot(Exports, color = "grey", size = 3) +
  autolayer(aus_exports_withMA, MA15, color = "red", size = 2)
ggsave("AusExportsMA15.png")

aus_exports_withMA |> autoplot(Exports, color = "grey", size = 3) +
  autolayer(aus_exports_withMA, MA17, color = "red", size = 2)
ggsave("AusExportsMA17.png")

#daily data
vic_elec
vic_elec_daily <- vic_elec |>
  mutate(Day = as_date(Time))

vic_elec_daily |>
  index_by(Day) |>
  summarize(AVGDemand = mean(Demand)) -> vic_elec_daily

vic_elec_daily |> autoplot()
vic_elec_daily |> head(n = 366) ->vic_elec_daily

vic_elec_daily |> autoplot()
vic_elec_daily |> slice(90:180) -> vic_elec_daily
vic_elec_daily |> autoplot() + geom_point()
ggsave("VicElec_DailyShort.png")

vic_elec_daily |>
  mutate(MA3 = slider::slide_dbl(AVGDemand, mean, .before=1, .after = 1, .complete = TRUE)) |>
  mutate(MA5 = slider::slide_dbl(AVGDemand, mean, .before=2, .after = 2, .complete = TRUE)) |>
  mutate(MA7 = slider::slide_dbl(AVGDemand, mean, .before=3, .after = 3, .complete = TRUE)) |>
  mutate(MA9 = slider::slide_dbl(AVGDemand, mean, .before=4, .after = 4, .complete = TRUE)) |>
  mutate(MA11 = slider::slide_dbl(AVGDemand, mean, .before=5, .after = 5, .complete = TRUE))  ->vic_elec_daily_withMA

vic_elec_daily_withMA |> autoplot(AVGDemand, color = "grey", size = 3) +
  autolayer(vic_elec_daily_withMA, MA3, color = "red", size = 2)
ggsave("VicElecMA03.png")

vic_elec_daily_withMA |> autoplot(AVGDemand, color = "grey", size = 3) +
  autolayer(vic_elec_daily_withMA, MA5, color = "red", size = 2)
ggsave("VicElecMA05.png")


vic_elec_daily_withMA |> autoplot(AVGDemand, color = "grey", size = 3) +
  autolayer(vic_elec_daily_withMA, MA7, color = "red", size = 2)
ggsave("VicElecMA07.png")


vic_elec_daily_withMA |> autoplot(AVGDemand, color = "grey", size = 3) +
  autolayer(vic_elec_daily_withMA, MA9, color = "red", size = 2)
ggsave("VicElecMA09.png")

vic_elec_daily_withMA |> autoplot(AVGDemand, color = "grey", size = 3) +
  autolayer(vic_elec_daily_withMA, MA11, color = "red", size = 2)
ggsave("VicElecMA11.png")


vic_elec_daily_withMA |> 
  mutate(MA21 = slider::slide_dbl(AVGDemand, mean, .before=10, .after = 10, .complete = TRUE)) |>
  mutate(MA25 = slider::slide_dbl(AVGDemand, mean, .before=12, .after = 12, .complete = TRUE))  ->vic_elec_daily_withMA


vic_elec_daily_withMA |> autoplot(AVGDemand, color = "grey", size = 3) +
  autolayer(vic_elec_daily_withMA, MA21, color = "red", size = 2)
ggsave("VicElecMA21.png")

vic_elec_daily_withMA |> autoplot(AVGDemand, color = "grey", size = 3) +
  autolayer(vic_elec_daily_withMA, MA25, color = "red", size = 2)

beer |> autoplot() + geom_point()
beer |> mutate(MA4 = slider::slide_dbl(Beer, mean, .before = 2, .after = 1, complete = TRUE)) |>
  mutate(MA2x4 = slider::slide_dbl(MA4, mean, .before = 0, .after = 1, complete = TRUE)) ->beerMA

beerMA |> autoplot(Beer, color = "grey", size = 3) +
  autolayer(beerMA, MA4, color = "red", size = 2) +
  autolayer(beerMA, MA2x4, color = "green", size = 2)

beerMA_Short <- beerMA |> head(n = 32)
beerMA_Short |> autoplot(Beer, color = "grey", size = 3) +
  autolayer(beerMA_Short, MA4, color = "red", size = 2) +
  autolayer(beerMA_Short, MA2x4, color = "green", size = 2)
ggsave("Beer2x4.png")


