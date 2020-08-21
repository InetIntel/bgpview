# BGPView

BGPView is a set of highly optimized data structures and libraries for
(re-)construction, transport and analysis of BGP "routing tables".

## Background

For a detailed description of BGPView, see Section 6.2 of the
[BGPStream paper](https://www.caida.org/publications/papers/2016/bgpstream/bgpstream.pdf).

At a high level, the goal of BGPView is to facilitate the inference of
"Global" routing tables at a finer granularity than the RIB dumps
provided by the RouteViews and RIPE RIS projects. For example,
currently RouteViews collectors export a snapshot of their RIB (a "RIB
dump") every 2 hours -- for RIPE RIS this is once every 8 hours. For
applications where latency matters (e.g., near-realtime event
detection), and/or are interested in observing short-duration events,
they cannot rely on these RIB dumps alone (i.e., using RouteViews
data, they would only be able to observe events that last at least 2
hours, and with up to 2 hours of latency).

The normal approach to solving this problem is to write some code that
starts with a RIB dump, and then incrementally applies update
information to approximate the state of each peer's routing table at
any point in time. Then, depending on the application, one can either
react to specific events (e.g., a prefix is announced, withdrawn,
etc.) or, periodically walk through these routing tables and perform
analysis on the entire "global" routing table (or, "inferred"
RIB). BGPView is designed to make it simple to write analysis code in
the latter model, with all of the details of obtaining the raw BGP
data, processing it, and inferring the routing table for each peer are
abstracted away from the user. The user is instead able to focus on
writing an analysis kernel (a "BGPView Consumer") that is invoked
every time a new inferred RIB (a "BGPView") is available.

There are two primary modes of operation for BGPView: realtime, and
offline.

In realtime mode, there is a set of distributed processes that:
 - obtain the BGP data (using
   [BGPStream](https://bgpstream.caida.org)) as soon as it is made
   available by the upstream projects
 - process it, and
 - periodically (every 5 min in CAIDA's reference deployment) publish
   fragments of each view to a Kafka cluster.
Users can then connect their analysis modules to this cluster using
the BGPView toolset, and as soon as a view becomes available, their
code will analyze it.

In offline mode the BGPView components are similar, but rather than a
distributed set of many processes that communicate via Kafka,
everything runs within a single process. The views that are generated
are passed in-memory to the configured consumers. While this is a
convenient method for using the same analysis code (consumers) to do
longitudinal analysis, it does require significant memory (often >20
GB when using all collectors), and is not a parallelized application,
so processing times are roughly the sum of all components that operate
in the realtime pipeline (whereas, in realtime these components are
truly pipelined).

## Quick Start

### Debian/Ubuntu Packages

The easiest way to install BGPView and its dependencies is from
CAIDA's apt package mirror.

```
curl https://pkg.caida.org/os/ubuntu/boostrap.sh | bash
sudo apt install bgpview
```
Of course you should first manually inspect the `bootstrap.sh` script
before executing it.

### Building From Source

You will need to first install dependencies:

 - [libbgpstream (>= v2.0.0)](https://bgpstream.caida.org)
 - [libtimeseries (>= v1.0.0)](https://github.com/CAIDA/libtimeseries)
 - [libipmeta (>= v3.0.0)](https://github.com/CAIDA/libipmeta)
 - [libwandio (>= v4.2.0)](https://research.wand.net.nz/software/libwandio.php)
 - [librdkafka (>= v0.11.3)](https://github.com/edenhill/librdkafka)

On Ubuntu/Debian systems, this means something like
```
sudo apt install libbgpstream2-dev libtimeseries0-dev \
  libipmeta2-dev libwandio1-dev librdkafka-dev
```
This assumes you have added the CAIDA package archive to apt using the
bootstrap command above.

One you have installed the dependencies, download the BGPView source,
either from the
[GitHub releases page](https://github.com/CAIDA/bgpview/releases), or
by cloning the GitHub repo.

If you cloned from GitHub, you will first need to:
```
./autogen.sh
```

Then:
```
./configure
make
sudo make install
```

This will install the `bgpview-consumer` tool which is used to run the
consumers against a source of BGPViews.

There is also a `bvcat` tool that will be installed. This is used to
convert the binary files generated by the `archiver` consumer into
ASCII format.

## Realtime Analysis

### CAIDA's Public BGPView feed

### Running a private BGPView deployment

## Offline Analysis

### One-off Processing

### Spark-managed Processing

## Available Consumers

All consumer code is located in the
[lib/consumers/](https://github.com/CAIDA/bgpview/tree/master/lib/consumers)
directory. Consumer source files are named `bvc_<consumer>.[ch]`.

To get a list of consumers built into a specific bgpview-consumer
binary, run it without arguments.

Currently the following consumers are part of the official BGPView package:

### Utility Consumers
 - `archiver`
 - `viewsender`
 - `visibility`

### Prefix-Origin Consumers
 - `peerpfxorigins`
 - `pfx2as`

### BGP Hijacks Observatory Consumers
 - `edges`
 - `moas`
 - `subpfx`
 - `announcedpfxs`
 - `pfxorigins`
 - `routedspace`
 - `triplets`

### IODA Consumers
 - `perasvisibility`
 - `pergeovisibility`

### Test/Template Consumers
 - `test`
 - `myviewprocess`

### Misc Consumers
 - `pathchange`
 - `perfmonitor`


## Writing a New Consumer
