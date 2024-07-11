# Remember to insert license in the ENV command below
#
# cd should be a folder containing this dockerfile, the armfm installation folder, and anything else:
#  | Dockerfile
#  | FastModels_11-21-015_Linux64_armv8l
#
# I can't remember, but I don't think these are needed for installation:
#  | FVP_ARM_Std_Library_11.21_15_Linux64_armv8l
#  | FastModels_ThirdParty_IP_11-21_Linux64_armv8l
#  | arm-fastmodels-boot (git clone the example repo)
#
# To build the image (once):
# docker build . -t armfm_img --progress=plain
#
# To make a container (once):
# docker run -it -v $PWD:/host --name armfmtest armfm_img
#
# To run an existing container:
# docker start armfmtest

FROM --platform=linux/arm64/v8 ubuntu:20.04
RUN mkdir /armdump
COPY . /armdump
ENV ARMLMD_LICENSE_FILE=insert-license-here
RUN TZ=America/Vancouver ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone
RUN apt update -y && apt upgrade -y
RUN apt install gcc-9 lsb libsm6 libxcursor1 libxft2 libxrandr2 libxt6 libxinerama-dev git vim -y
WORKDIR /armdump/FastModels_11-21-015_Linux64_armv8l
RUN ls
RUN ./setup.bin --i-accept-the-end-user-license-agreement
WORKDIR /

# executed whenever a shell is opened (adds simgen and probably other bins to PATH)
# If there are include errors (e.g. no such file or directory "pv/whatever.h") then this isn't working
RUN echo "\n\n. /root/ARM/SystemC/Accellera/etc/setup.sh && . /root/ARM/FastModelsTools_11.21/source_all.sh\n" >> ~/.bashrc

# executed on each "docker run"
CMD /bin/bash
