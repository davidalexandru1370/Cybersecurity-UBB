library(fpp3)
library(tidyverse)

climate <- read_csv("DailyDelhiClimate.csv")
climate
climate_ts <- climate |> as_tsibble(index = date)
climate_ts
climate_ts |> autoplot(meanpressure)
ggsave("ClimateMeanPressure.png")

climate_ts |> filter(year(date) < 2016) |> autoplot(meanpressure)

max(climate_ts$meanpressure)
max(climate_ts$meanpressure[1:1000])

position <- which(climate_ts$meanpressure == max(climate_ts$meanpressure))
position

climate_ts$meanpressure[1183] <- 1200
climate_ts |> autoplot(meanpressure)

climate_ts_short <- climate_ts |> filter(year(date) == 2016, month(date) < 5)
climate_ts_short |> autoplot(meanpressure)

climate_ts_short |> head(n = 21) |> autoplot(meanpressure)
climate_ts_short |> gg_season(meanpressure, period= 7)
climate_ts_short |> head(n = 80) |> gg_season(meanpressure, period = 7)
climate_ts_short |> head(n = 80) |> gg_season(meanpressure, period = "month")

climate_ts |> head (n = 1000) |> gg_season(meanpressure, period = 7)
climate_ts |> head (n = 1000) |> gg_season(meanpressure, period = "month")

#based on seasonal subseries plots it is not seasonal data.
#Any odd m is OK for moving average

climate_ts_short <- climate_ts_short |>
  mutate(MA7 = slider::slide_dbl(meanpressure, mean, .before = 3, .after = 3, .complete = TRUE)) |>
  mutate(MA11 = slider::slide_dbl(meanpressure, mean, .before = 5, .after = 5, .complete = TRUE)) |>
  mutate(MM7 = slider::slide_dbl(meanpressure, median, .before = 3, .after = 3, .complete = TRUE))


climate_ts_short |> autoplot(meanpressure, color = "grey", size = 3) +
  autolayer(climate_ts_short, MA7, color = "red", size = 2) +
  autolayer(climate_ts_short, MA11, color = "green", size = 2)
ggsave("ClimateOutlier.png")

climate_ts_short |> autoplot(meanpressure, color = "grey", size = 3) +
  autolayer(climate_ts_short, MA7, color = "red", size = 2) +
  autolayer(climate_ts_short, MM7, color = "green", size = 2)
ggsave("ClimateMovingMedian.png")

#to see where the actual points are
climate_ts_short2 <- climate_ts_short |> head (n= 21)
climate_ts_short2

climate_ts_short2 |> autoplot(meanpressure, color = "grey", ) +
  autolayer(climate_ts_short2, MA7, color = "red") +
  autolayer(climate_ts_short2, MM7, color = "green") + geom_point() +
  geom_point(mapping = aes(x = climate_ts_short2$date, y = climate_ts_short2$MM7), color = "darkgreen") +
  geom_point(mapping = aes(x = climate_ts_short2$date, y = climate_ts_short2$MA7), color = "darkred")
ggsave("ClimateMovingMedianPoints.png")

climate_ts_short <- climate_ts_short |>
  mutate(MM10 = slider::slide_dbl(meanpressure, median, .before = 5, .after = 4, complete = TRUE))

climate_ts_short2 <- climate_ts_short |> head (n= 21)
climate_ts_short2 |> autoplot(meanpressure, color = "grey", ) +
  autolayer(climate_ts_short2, MM10, color = "red") +
  geom_point(mapping = aes(x = date, y = MM10), color = "darkred") 
ggsave("ClimateMovingMedianPointsEven.png")

#classical decomposition
beer <- aus_production |> select(Beer)
beer |> autoplot()
ggsave("BeerPlot.png")

beerDecomp <- beer |> 
  model(d = classical_decomposition(Beer, type = "additive"))

beerDecomp |> components() 
beerDecomp |> components() |> autoplot()
ggsave("BeerComponents.png")

beerDecomp |> components() |>
  ACF(random) |> autoplot()
ggsave("BeerRandomACF.png")


#try a box-cox transformation
beer |> features(Beer, guerrero) -> lambda
lambda

beer <- beer |>
  mutate(BeerTr = box_cox(Beer, lambda))
beer

beerDecomp2 <- beer |> 
  model(d = classical_decomposition(BeerTr, type = "additive"))

beerDecomp2 |> components() 
beerDecomp2 |> components() |> autoplot()
ggsave("BeerComponents.png")

beerDecomp2 |> components() |>
  ACF(random) |> autoplot()
ggsave("BeerRandomACF.png")


beer |> autoplot()

#beer short
beerShort <- beer |>
  filter(year(Quarter) >= 1962, year(Quarter)< 1976)

beerShort
beerShort |> autoplot() + geom_point()
ggsave("BeershortPlot.png")

beerShortDecomp <- beerShort |>
  model(d = classical_decomposition(Beer, type = "additive"))

beerShortDecomp |> components() |> autoplot()
ggsave("BeerShortComponents.png")

beerShortDecomp |> components() |> 
  ACF(random) |> autoplot()
ggsave("BeerShort_RandomACF.png")


#beer recent
beerRecent <- beer |> tail(n = 56)
beerRecent
beerRecent |> autoplot() + geom_point()
ggsave("BeerRecentPlot.png")

beerRecentDecomp <- beerRecent |>
  model(d = classical_decomposition(Beer, type = "additive"))

beerRecentDecomp |> components() |> autoplot()
ggsave("BeerRecentComponents.png")

beerRecentDecomp |> components() |> 
  ACF(random) |> autoplot()
ggsave("BeerRecent_RandomACF.png")


beerRecentDecomp |> components() |> autoplot(trend, color = "red", size = 1.5) +
  autolayer(beerRecent, Beer, color = "grey", size = 2)

#Compare the two seasons
beerShortDecomp |> components() |> select(seasonal) |> 
  head(n = 8) |>
  mutate(Index = seq(from = 1, to = 8, by = 1)) |>
  index_by(Index) -> shortSeason
shortSeason

beerRecentDecomp |> components() |> select(seasonal) |> 
  head(n = 10) |> tail(n = 8) |>
  mutate(Index = seq(from = 1, to = 8, by = 1)) |>
  index_by(Index) -> recentSeason
recentSeason

ggplot() +
  geom_line(mapping = aes(x = shortSeason$Index, y = shortSeason$seasonal), color = "red") +
  geom_line(mapping = aes(x = recentSeason$Index, y = recentSeason$seasonal), color = "blue") +
  geom_point(mapping = aes(x = shortSeason$Index, y = shortSeason$seasonal)) + 
  geom_point(mapping = aes(x = recentSeason$Index, y = recentSeason$seasonal))  
  

#antidiabetic
A10 <- PBS |>
  filter(ATC2 == "A10") |>
  select(Month, Concession, Type, Cost) |>
  summarize(TotalCost = sum(Cost)) |>
  mutate(Cost = TotalCost / 1000000)

A10 |> autoplot(Cost) + geom_point()
ggsave("A10Plot.png")
A10Decomp <- A10 |> model(d = classical_decomposition(Cost, type = "multiplicative")) 
A10Decomp |> components()

A10Decomp |> components() |> autoplot()
ggsave("A10Components.png")

A10Decomp |> components() |>
  ACF(random) |> autoplot()
ggsave("A10RandomACF.png")


#X11
us_retail_employment

x_11_decomp <- us_retail_employment |>
  model(x11 = X_13ARIMA_SEATS(Employed ~ x11()))
x_11_decomp |> components() |> autoplot()
x_11_decomp |> components()
x_11_decomp |> components() |> tail(n = 10)

x_11_comp <- x_11_decomp |> components()
ggsave("EmploymentX_11.png")

?X_13ARIMA_SEATS

ggplot(data = x_11_comp, mapping = aes(x = Month)) +
  geom_line(mapping = aes(y = Employed, color = "Original data")) +
  geom_line(mapping = aes(y = season_adjust, color = "Seasonally adjusted data"), linewidth = 2) +
  geom_line(mapping = aes(y = trend, color = "Trend component"), linewidth = 2) +
  labs(title = "X11 Decomposition - Trend and Seasonally Adjusted components")      
ggsave("EmployedX11_TrendSeas.png")

#seasonalma
#trendma
#Expected a name or a quote or a list of names or quotes, not "11" Valid choices of seasonal filter are 
#s3x1, s3x3, s3x5, s3x9, s3x15, stable, msr, or x11default.

x_11_decomp2 <- us_retail_employment |>
  model(x11 = X_13ARIMA_SEATS(Employed ~ x11(seasonalma = "s3x15")))
x_11_decomp2 |> components() 
x_11_decomp2 |> components() |> autoplot()

#- Length of Henderson trend filter must be a positive odd integer.
x_11_decomp3 <- us_retail_employment |>
  model(x11 = X_13ARIMA_SEATS(Employed ~ x11(trendma = 23)))
x_11_decomp3 |> components() 
x_11_decomp3 |> components() |> autoplot()
x_11_decomp3 |> components() |> tail(n = 10)



x_11_decomp3 <- us_retail_employment |>
  model(x11 = X_13ARIMA_SEATS(Employed ~ x11(seasonalma = "s3x1")))
x_11_decomp3 |> components() 
x_11_decomp3 |> components() |> autoplot()
x_11_comp3<- x_11_decomp3 |> components()

x_11_decomp4 <- us_retail_employment |>
  model(x11 = X_13ARIMA_SEATS(Employed ~ x11(seasonalma = "s3x15")))
x_11_decomp4 |> components() 
x_11_decomp4 |> components() |> autoplot()
x_11_comp4 <- x_11_decomp4 |> components()

ggplot() +
  geom_line(mapping = aes(x =x_11_comp3$Month, y = x_11_comp3$seasonal), color = "red", size = 1.5, alpha = 0.4) +
  geom_line(mapping = aes(x =x_11_comp4$Month, y = x_11_comp4$seasonal), color = "blue", size = 1.5, alpha = 0.4) 
ggsave("EmployedS3x1vs3x15.png")  

#SEATS
seats_dcmp <- us_retail_employment |>
  model(seats=X_13ARIMA_SEATS(Employed ~ seats())) |>
  components()
autoplot(seats_dcmp)
seats_dcmp 
ggsave("EmployedSeats.png")


#LOESS
?loess
us_retail_employment_index <- us_retail_employment |>
  mutate(Nr = seq(from = 1, to = 357, by= 1))
us_retail_employment_index |> view()
us_retail_employment_index |> autoplot(Employed)


loess_model <- loess( Employed ~ Nr, data = us_retail_employment_index, span = 0.1)
loess_model 
us_retail_employment_index <- us_retail_employment_index |>
  mutate(Smoothed = predict(loess_model))
us_retail_employment_index

us_retail_employment_index |> ggplot(mapping = aes(x = Nr)) +
  geom_line(mapping = aes(y = Smoothed), color = "red") +
  geom_point(mapping = aes(y = Employed), color = "blue") + 
  geom_line(mapping = aes(y = Employed), color = "grey")
ggsave("EmployedLOESS.png")  

loess_model <- loess( Employed ~ Nr, data = us_retail_employment_index, span = 0.6)
loess_model 
us_retail_employment_index <- us_retail_employment_index |>
  mutate(Smoothed = predict(loess_model))
us_retail_employment_index

us_retail_employment_index |> ggplot(mapping = aes(x = Nr)) +
  geom_line(mapping = aes(y = Smoothed), color = "red") +
  geom_point(mapping = aes(y = Employed), color = "blue") + 
  geom_line(mapping = aes(y = Employed), color = "grey")

?STL
stl_dcm <- us_retail_employment |>
  model(Stl = STL(Employed)) |>
  components()
stl_dcm |> autoplot()
stl_dcm
ggsave("EmployedSTL.png")


stl_dcm2 <- us_retail_employment |>
  model(Stl = STL(Employed ~ trend(window = 5))) |>
  components()
stl_dcm2 |> autoplot()
ggsave("EmployedSTLTrend-5.png")

stl_dcm3 <- us_retail_employment |>
  model(Stl = STL(Employed ~ trend(window = 51))) |>
  components()
stl_dcm3 |> autoplot()
ggsave("EmployedSTLTrend-51.png")


stl_dcm4 <- us_retail_employment |>
  model(Stl = STL(Employed ~ trend(window = 501))) |>
  components()
stl_dcm4 |> autoplot()
ggsave("EmployedSTLTrend-501.png")

stl_dcm5 <- us_retail_employment |>
  model(Stl = STL(Employed ~ season(window = 5))) |>
  components()
stl_dcm5 |> autoplot()
ggsave("EmployedSTLSeason-5.png")


stl_dcm6 <- us_retail_employment |>
  model(Stl = STL(Employed ~ season(window = 25))) |>
  components()
stl_dcm6 |> autoplot()
ggsave("EmployedSTLSeason-25.png")

stl_dcm7 <- us_retail_employment |>
  model(Stl = STL(Employed ~ season(window = "periodic"))) |>
  components()
stl_dcm7 |> autoplot()
ggsave("EmployedSTLSeasonPeriodic.png")


stl_dcm8 <- us_retail_employment |>
  model(Stl = STL(Employed ~ trend(window = 13) + season(window = "periodic"))) |>
  components()
stl_dcm8 |> autoplot()
ggsave("EmployedSTLSeasonTrend.png")

stl_dcm |> autoplot()

stl_dcm9 <- us_retail_employment |>
  model(stl = STL(Employed, iterations = 1)) |> components() 
stl_dcm9 |> autoplot()
stl_dcm9 |> view()

stl_dcm10 <- us_retail_employment |>
  model(stl = STL(Employed, iterations = 15)) |> components() 
stl_dcm10 |> autoplot()
stl_dcm10 |> view()

#robust
stl_climate <- climate_ts_short |>
  model(Stl = STL(meanpressure)) |> components()
stl_climate |> autoplot()
ggsave("ClimateSTL.png")

stl_climate2 <- climate_ts_short |>
  model(Stl = STL(meanpressure, robust = TRUE)) |> components()
stl_climate2 |> autoplot()
ggsave("ClimateSTLRobust.png")


#period
stl_dcm11 <- us_retail_employment |>
  model(stl = STL(Employed ~ season(period = 6))) |> components()
stl_dcm11 |> autoplot()
ggsave("EmployedSTL_SeasonPEriod6.png")
stl_dcm11 |> ACF(remainder) |> autoplot()

stl_dcm12 <- us_retail_employment |>
  model(stl = STL(Employed ~ season(period = c(6, 12)))) |> components()
stl_dcm12 |> autoplot()
ggsave("EmployedSTL_SeasonPEriod6-12.png")


#compare beer decompositions
clDecmp <- beer |>
  model(cd = classical_decomposition(Beer, type = "additive")) |> components()
clDecmp |> autoplot()
clDecmp |> ACF(random) |> autoplot()

x11Decmp <- beer |>
  model(x11 = X_13ARIMA_SEATS(Beer ~ x11())) |> components()
x11Decmp |> autoplot()
x11Decmp |> ACF(irregular) |> autoplot()

seatsDecmp <- beer |>
  model(seats = X_13ARIMA_SEATS(Beer ~ seats())) |> components()
seatsDecmp |> autoplot()
seatsDecmp |> ACF(irregular) |> autoplot()

stlDecmp <- beer |>
  model(stl = STL(Beer)) |> components()
stlDecmp |> autoplot()
stlDecmp |> ACF(remainder) |> autoplot()

#MSTL
?stl
vic_elec
vic_elec |>
  index_by(hour = floor_date(Time, "hour")) |>
  summarize(AVGDemand = mean(Demand)) -> vic_elec_daily

vic_elec_daily
vic_elec_daily <- vic_elec_daily |>
  filter(year(hour) == 2012, month(hour) <= 6)

vic_elec_daily |> autoplot()

vic_elec_daily |> model(mstl = STL(AVGDemand ~ season(period = c(24, 24*7, 24*31)))) |> components() |> autoplot()
ggsave("VicElec_STL_DayWeek.png")


#features
tourism

tourism |>
  features(Trips, mean)

tourism |>
  features(Trips, list(Mean = mean))

tourism |>
  features(Trips, list(Mean = mean, Min = min))

tourism |>
  features(Trips, list(Mean = mean, Min = min)) |>
  arrange(Mean)

tourism |>
  features(Trips, list(Mean = mean, Min = min)) |>
  arrange(desc(Mean))

tourism |>
  features(Trips, quantile) |>
  arrange(`25%`)

tourism |>
  features(Trips, feat_acf)
