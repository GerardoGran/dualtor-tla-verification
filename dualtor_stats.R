#!/usr/bin/env Rscript

library(tidyverse)
library(ggplot2)

args <- commandArgs(trailingOnly = TRUE)

svg(gsub(".csv$", ".svg", args[1]))


data <- read.csv(header = TRUE, sep = "#", file = "dualtor_stats.csv")

summary = summarise(group_by(data,flags),
                    One = round(mean(one), 0),
                    Both = round(mean(both, 0)),
                    None = round(mean(none, 0)),
                    Failures = round(mean(failures, 0))
)

df <- pivot_longer(summary, cols=2:4, names_to = "Active", values_to = "States")
df$Active<-replace(df$Active, df$Active=="None", 0)
df$Active<-replace(df$Active, df$Active=="One", 1)
df$Active<-replace(df$Active, df$Active=="Both", 2)

ggplot(NULL, aes(y=States, x=flags)) + 
  geom_bar(data = df, aes(fill=Active), position="dodge", stat="identity") +
  geom_bar(data = df, aes(y=Failures, x=flags), position="dodge", stat="identity", alpha = 0.2) +
  theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust=0.5)) +
  labs(title = paste("Samples: ", nrow(data))) +
  xlab("Failures")
