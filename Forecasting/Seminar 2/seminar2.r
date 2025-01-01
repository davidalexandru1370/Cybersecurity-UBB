library("tidyverse")
library("fpp3")
# 1
sunspots <- read.csv("./Seminar 2/Sunspots.csv")
sunspots_tsibble <- as_tsibble(sunspots, index = X)

# a) Rename the “Monthly Mean Total Sunspot Number” column into “Sunspots”. (Hint: when you
# need to use column names containing several words, you need to put them between ` `)
print(head(sunspots_tsibble, n = 10))
sunspots_tsibble <- rename(sunspots_tsibble, `Sunspots` = `Monthly.Mean.Total.Sunspot.Number`)

# print the first 10 rows of the dataset
print(head(sunspots_tsibble, n = 10))

# b) Drop the column containing the line numbers
sunspots_tsibble <- select(sunspots_tsibble, -X)

# c) Plot the time series of sunspots.
autoplot(sunspots_tsibble, Sunspots)

# d) What is the frequency of your tsibble data? Does this seem correct to you?

# e) Transform your Date column, so that it has a monthly frequency (Hint: use the yearmonth function)
sunspots_tsibble <- mutate(sunspots_tsibble, Date = yearmonth(Date))

# f) Get the summary of the Sunspots attribute.
summary(sunspots_tsibble$Sunspots)
print(summary)

# g) Autoplot your data
# h) Look at the autoplot of the entire data. Does it have trends?
# i) Look at the autoplot of the entire data. Does it have seasons? If yes, determine their exact length.
# j) Look at the autoplot of the entire data. Does it have cycles? If yes, try to determine an approximate
# average length for them.
autoplot(sunspots_tsibble, Sunspots)


# k) Create a seasonal plot. Does it confirm your answer to the previous 3 points (about the existence
# of trend, cycle and season)?
print(gg_season(sunspots_tsibble, Sunspots, period = 12))
# display seasonal plot
