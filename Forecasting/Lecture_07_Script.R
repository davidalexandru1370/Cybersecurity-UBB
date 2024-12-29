library(fpp3)
library(tidyverse)

tourism
tourism |> features(Trips, feat_acf) |> view()

tourism |> features(Trips, feat_acf) |>
  arrange(desc(acf10)) |> view()

tourism |> filter(Region == "Bundaberg", Purpose == "Business") |> 
  autoplot(Trips) + geom_point()

tourism |> 
  filter(Region == "Bundaberg", Purpose == "Business") |> 
  ACF(Trips) |> autoplot()


tourism |> filter(Region == "Australia's North West", Purpose == "Business") |> 
  autoplot(Trips) + geom_point()

tourism |> 
  filter(Region == "Australia's North West", Purpose == "Business") |> 
  ACF(Trips) |> autoplot()

#STL features

tourism_NW <- tourism |> 
  filter(Region == "Australia's North West", Purpose == "Business") 

tourism_B <- tourism |> 
  filter(Region == "Bundaberg", Purpose == "Business") 


tourism_NW |> model(stl = STL(Trips)) |> components() -> tourism_NW_comp
tourism_NW_comp |> autoplot()
var(tourism_NW_comp$remainder) -> vRemainder_NW
var(tourism_NW_comp$season_adjust) -> vSeason_NW
trendStrengthNW <- 1 - (vRemainderNW / (vSeasonNW))
trendStrengthNW

tourism_B |> model(stl = STL(Trips)) |> components() -> tourism_B_comp
tourism_B_comp |> autoplot()
var(tourism_B_comp$remainder) -> vRemainder_B
vRemainder_B
var(tourism_B_comp$season_adjust) -> vSeason_B
vSeason_B
trendStrengthB <- 1 - (vRemainder_B/ (vSeason_B))
trendStrengthB

tourism |> features(Trips, feat_stl) |> view()

tourism |> features(Trips, feat_stl) |> arrange(desc(trend_strength)) |> view()

# plot trend_Strength vs seasonal strength

tourism |> 
  features(Trips, feat_stl) |>
  ggplot(mapping = aes(x = trend_strength, y = seasonal_strength_year, col = Purpose)) +
  geom_point(size = 3.5)

ggsave("Tourism_TrendvsSeasonStrengh.png")

tourism |> 
  features(Trips, feat_stl) |>
  ggplot(mapping = aes(x = trend_strength, y = seasonal_strength_year, col = Purpose)) +
  geom_point(size = 3.5) + 
  facet_wrap(vars(State))

ggsave("Tourism_TrendvsSeasonStrenghByState.png")

#strongest seasonal component
max_strength <- tourism |>
  features(Trips, feat_stl) |>
  filter(seasonal_strength_year == max(seasonal_strength_year))
max_strength

max_strength |> left_join(tourism, by = c("State", "Region", "Purpose"), multiple = "all") |>
  ggplot(mapping = aes(x = Quarter, y = Trips)) +
  geom_line() +
  geom_point()  

ggsave("StrongSeasonal.png")

max_strength |> left_join(tourism, by = c("State", "Region", "Purpose"), multiple = "all") |>
  ggplot(mapping = aes(x = Quarter, y = Trips)) +
  geom_line() +
  geom_point()  +
  facet_grid(vars(State, Region, Purpose))

#allfeatures
tourism_features <- tourism |>
  features(Trips, feature_set(pkgs = "feasts"))
tourism_features |> view()

tourism_features

#Simple forecasting methods
aus_production
bricksData <- aus_production |>
  filter(year(Quarter) >= 1970, year(Quarter) <= 2004) |>
  select(Bricks)

bricksData |> autoplot() + geom_point()
ggsave("BricksPlot.png")

bricksData |>
  model(MEAN(Bricks)) -> bricksModel
bricksModel
tidy(brickModel)

#let's forecast for 10 periods
brickModel |> 
  forecast(h = 10) -> brickForecast
brickForecast
brickForecast |>
  autoplot(level = NULL) +
  autolayer(bricksData, Bricks)
ggsave("BricksMeanForecast.png")

bricksData |>
  model(NAIVE(Bricks)) -> brickNaiveModel
tidy(brickNaiveModel)
brickNaiveModel |>
  forecast(h = "3 years") -> brickNaiveForecast

brickNaiveForecast
brickNaiveForecast |>
  autoplot(level = NULL) + 
  autolayer(bricksData, Bricks)
ggsave("BricksNaiveForecast.png")

#Random walk process is the same as the naive method.
bricksData |>
  model(RW(Bricks)) -> brickRWModel
tidy(brickRWModel)
brickRWModel |>
  forecast(h = "3 years") -> brickRWForecast

brickRWForecast
brickRWForecast |>
  autoplot(level = NULL) + 
  autolayer(bricksData, Bricks)

bricksData |>
  model(SNAIVE(Bricks ~ lag("year"))) -> bricksSNaiveModel
tidy(bricksSNaiveModel)
bricksSNaiveModel |>
  forecast(h = 10) -> bricksSNaiveForecast
bricksSNaiveForecast
bricksSNaiveForecast |>
  autoplot(level = NULL) +
  autolayer(bricksData, Bricks)
ggsave("BricksSeasonalNaive.png")


vic_elec |> head (n = 150) -> vic_elec_short
vic_elec_short |> autoplot()
vic_elec_short |> model(SNAIVE(Demand ~ lag("day"))) -> vic_elec_SNaiveDayModel
vic_elec_SNaiveDayModel |> forecast(h = "7 days") -> vic_elec_SNaiveDayForecast
vic_elec_SNaiveDayForecast |>
  autoplot(level=  NULL) +
  autolayer(vic_elec_short, Demand)
ggsave("VicElec_SeasonalNaiveForecastDay.png")

vic_elec |> head (n = 1500) -> vic_elec_short
vic_elec_short |> autoplot()
vic_elec_short |> model(SNAIVE(Demand ~ lag("week"))) -> vic_elec_SNaiveDayModel
vic_elec_SNaiveDayModel |> forecast(h = "2 weeks") -> vic_elec_SNaiveDayForecast
vic_elec_SNaiveDayForecast |>
  autoplot(level=  NULL) +
  autolayer(vic_elec_short, Demand)
ggsave("VicElec_SeasonalNaiveForecastWeek.png")

vic_elec |> head (n = 1500) -> vic_elec_short
vic_elec_short |> autoplot()
vic_elec_short |> model(SNAIVE(Demand ~ lag("month"))) -> vic_elec_SNaiveDayModel
vic_elec_SNaiveDayModel |> forecast(h = "1 month") -> vic_elec_SNaiveDayForecast
vic_elec_SNaiveDayForecast |>
  autoplot(level=  NULL) +
  autolayer(vic_elec_short, Demand)
ggsave("VicElec_SeasonalNaiveForecastMonth.png")

bricksData |> 
  model(RW(Bricks ~ drift())) -> bricksDriftModel
tidy(bricksDriftModel)

bricksDriftModel |> 
  forecast(h = 10) -> bricksDriftForecast

bricksDriftForecast
bricksDriftForecast |>
  autoplot(level = NULL) + 
  autolayer(bricksData, Bricks)
ggsave("BricksDriftForecast.png")


bricksDriftModel |> 
  forecast(h = 100) -> bricksDrift2Forecast

bricksDrift2Forecast
bricksDrift2Forecast |>
  autoplot(level = NULL) + 
  autolayer(bricksData, Bricks)


#Where does the time series end?
bricksData
bricksData |> head(n = 139) -> bricksShort
bricksDriftModel2 <- bricksShort |> model(RW(Bricks ~ drift()))
tidy(bricksDriftModel2)

bricksDriftModel2 |> 
  forecast(h = 100) -> bricksDriftForecast2

bricksDriftForecast2
bricksDriftForecast2 |>
  autoplot(level = NULL) + 
  autolayer(bricksData, Bricks)


bricksDriftForecast2 |>
  autoplot(level = NULL) + 
  autolayer(bricksData, Bricks) +
  autolayer(bricksDrift2Forecast, .mean, level=  NULL)

#all 4 models
aus_production |> autoplot(Bricks) + geom_point()
aus_production |> tail(n = 25)

#between 1992 and  2002
bricksTrainData <- aus_production |>
  filter(year(Quarter) >= 1992 & year(Quarter) < 2002) |>
  select(Bricks)

bricksAllData = aus_production |>
  filter(year(Quarter) >= 1992 & !is.na(Bricks)) |>
  select(Bricks)

autoplot(bricksTrainData) +
  geom_point()
ggsave("BrickTrainData.png")

autoplot(bricksAllData) + 
  geom_point()
ggsave("BrickAllData.png")

bricksTrainData |> 
  model (mean = MEAN(Bricks), 
         naive = NAIVE(Bricks), 
         snaive = SNAIVE(Bricks ~ lag("year")), 
         drift = RW(Bricks ~ drift())) -> brickModels
tidy(brickModels)

brickModels |> 
  forecast(h = 14) -> brickForecast
view(brickForecast)

brickForecast |> 
  autoplot(bricksTrainData, level = NULL, size = 1.5) +
  autolayer (bricksAllData, colour = "black")  +
  guides(colour = guide_legend(title = "Forecasts"))
ggsave("BricksAllForecasts.png")

#Beer
beerTrainData <- aus_production |>
  filter(year(Quarter) > 1992 & year(Quarter) < 2007) |>
  select(Beer)

autoplot(beerTrainData) +
  geom_point()
ggsave("BeerTrainData.png")

beerAllData <- aus_production |>
  filter(year(Quarter) > 1992) |> 
  select(Beer)

autoplot(beerAllData) +
  geom_point()
ggsave("BeerAllData.png")

beerTrainData |> 
  model (mean = MEAN(Beer), 
         naive = NAIVE(Beer), 
         snaive = SNAIVE(Beer ~ lag("year")), 
         drift = RW(Beer ~ drift())) -> beerModels

beerModels |> 
  forecast(h = 14) -> beerForecast
view(beerForecast)

beerForecast |> 
  autoplot(beerTrainData, level = NULL, size = 1) +
  autolayer (beerAllData, colour = "black")  +
  guides(colour = guide_legend(title = "Forecasts"))   
ggsave("BeerAllForecasts.png")

#Google data
gafa_stock
gafa_stock |> 
  filter(Symbol == "GOOG"& year(Date) > 2014 & yearmonth(Date) <= yearmonth("2016 Jan")) -> googleData 
view(googleData)

#we need to know how many observations we have for train and test. 
#Since data is for trading days, this is not obvious
google2016DataCount <- googleData |> 
  filter(year(Date) == 2016) |> count()
google2016DataCount
google2015DataCount <- googleData |> 
  filter(year(Date) == 2015) |> count()
google2015DataCount


googleData <- googleData |>
  mutate(day = row_number()) |> #new attribute with consecutive numbers
  update_tsibble(index = day, regular = TRUE) |> #make the new attribute the index
  select(Close)

googleData
googleTrain <- googleData |> head(n = google2015DataCount$n[1])
googleTest <- googleData |> tail(n = google2016DataCount$n[1])


autoplot(googleTrain) +
  geom_point()
ggsave("GoogleTrain.png")

autoplot(googleTest) +
  geom_point()
ggsave("GoogleTest.png")

googleTrain |> 
  model (mean = MEAN(Close), 
         naive = NAIVE(Close), 
         drift = RW(Close ~ drift()),
        snaive = SNAIVE(Close ~ lag(5))) -> googleModels


googleModels |> 
  forecast(h = google2016DataCount$n[1]) -> googForecast
view(googForecast)

googForecast |> 
  autoplot(googleTrain, level = NULL, size = 1.5) +
  autolayer (googleData, colour = "black")  +
  guides(colour = guide_legend(title = "Forecasts"))
ggsave("GoogleAllForecast.png")

#Fitted values and residuals
google2015Data <- googleTrain #just rename it for clarity
google2015Data |>
  model(naive = NAIVE(Close)) |> 
  augment() -> google2015NaiveModel

google2015NaiveModel


#plot actual and fitted
google2015NaiveModel |>
  ggplot(mapping = aes(x = day)) +
  geom_line(mapping = aes(y = Close, color = "Data"), size = 1) +
  geom_line(mapping = aes(y = .fitted, color = "Fitted"), size = 1)
ggsave("GoogleNaiveFittedOrig.png")


autoplot(google2015NaiveModel, .innov) +
  geom_point()
ggsave("GoogleInnovationresiduals.png")

#check for a mean of 0 (it is 0.94 when the innovation residuals are between -34 and 93. It is OK)
google2015NaiveModel$.innov |> tail(251) |> mean()
google2015NaiveModel$.innov |> tail(251) |> min()
google2015NaiveModel$.innov |> tail(251) |> max()

google2015NaiveModel |> 
  ACF(.innov) |>
  autoplot() 
ggsave("GoogleInovResidACF.png")

google2015NaiveModel |>
  ggplot(mapping = aes(x = .innov)) +
  geom_histogram() 
ggsave("GoogleInnovResidHist.png")

google2015Data |>
  model(naive = NAIVE(Close)) |> 
  gg_tsresiduals()  ->p
ggsave("GoogleResidDiagnostics.png", plot = p)

google2015NaiveModel |>
  features (.innov, box_pierce, lag = 10)

google2015NaiveModel |>
  features(.innov, ljung_box, lag = 10)


google2015Data |>
  model(naive = NAIVE(Close)) |> 
  forecast(h = 10) #Normally distributed with Mean and variance


google2015Data |>
  model(naive = NAIVE(Close)) |> 
  forecast(h = 10)|> autoplot() 

google2015Data |>
  model(naive = NAIVE(Close)) |> 
  forecast(h = 10)|> 
  hilo()

google2015Data |>
  model(naive = MEAN(Close)) |> 
  forecast(h = 10)|> autoplot() 


google2015Data |> 
  model(NAIVE(Close)) |> 
  forecast(h = 10) |> 
  hilo(level = 99)


google2015Data |> 
  model(NAIVE(Close)) |> 
  forecast(h = 10) |> 
  autoplot(level = c(50, 99)) 

