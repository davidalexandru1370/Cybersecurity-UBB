# 1
sunspots <- read.csv("./Seminar 2/Sunspots.csv")
sunspots_tsibble <- as_tsibble(sunspots, index = X)

# a) Rename the “Monthly Mean Total Sunspot Number” column into “Sunspots”. (Hint: when you
# need to use column names containing several words, you need to put them between ` `)
print(head(sunspots_tsibble, n = 10))
sunspots_tsibble <- rename(sunspots_tsibble, `Sunspots` = `Monthly.Mean.Total.Sunspot.Number`)

# print the first 10 rows of the dataset
print(head(sunspots_tsibble, n = 10))

# b) Plot the time series of sunspots.

autoplot(sunspots_tsibble, Sunspots)
