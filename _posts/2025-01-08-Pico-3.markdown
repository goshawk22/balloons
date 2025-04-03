---
layout: post
title:  "Pico-3"
date:   2025-01-08 20:30:00 +0000
categories:
---
We used a new custom tracker design based around the Wio-E5 STM32WL (very similar to the RAK3172) module and Quectel L80R GPS module. It had a tx interval of 5 minutes and a spreading factor of SF10 was used. It was powered using a 500mAh battery taken from a disposable vape. The whole system weighed 23g, which probably ended up being 25g after all the tape and string we added.

The balloon was a qualatex 36" foil balloon, the same as was used for Pico-2. Free lift was about 3g.

The conditions were very still and the launch went smoothly.

The balloon rose at about 0.7m/s until it got to a float altitude of 5800m. Unfortunately the GPS module stopped working over night, probably due to the drop in temperature (it was about -28°C). It started working again once the sun came up (it warmed up to about 0°C).

It floated for a total of 48h, passing over France, Switzerland, Italy, Croatia, Montenegro, Albania and Greece. It then floated over the Mediterranean Sea towards Libya where we lost contact with it. It traveled a total of 3200km.

If you look at the data, you can see the balloon gained about 400m altitude over the day due to the helium in the balloon being heated.

We had an issue with Datacake, and this means the data doesn't contain location data. But the rest of the data can be found [here](https://raw.githubusercontent.com/goshawk22/balloons/refs/heads/master/data/pico-3.csv)
