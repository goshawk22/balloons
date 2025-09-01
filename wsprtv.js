// WSPR Telemetry Viewer (WSPR TV)
// https://github.com/wsprtv/wsprtv.github.io
//
// This file is part of the WSPR TV project.
// Copyright (C) 2025 WSPR TV authors.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published
// by the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
// This program uses WSPR Live, which includes the following
// disclaimer (see https://wspr.live):
//
// "... You are allowed to use the services provided on wspr.live for your
// own research and projects, as long as the results are accessible free of
// charge for everyone. You are not allowed to use this service for any
// commercial or profit-oriented use cases. The complete WSPR
// infrastructure is maintained by volunteers in their spare time, so
// there are no guarantees on correctness, availability, or stability of
// this service."

// Global vars
let map;  // Leaflet map object
let markers = [];
let marker_group;
let segment_group;
let last_marker;  // last marker in the displayed track
let selected_marker;  // currently selected (clicked) marker
let marker_with_receivers;  // marker that currently has receivers displayed

let data = [];  // raw wspr.live telemetry data
let spots = [];  // merged / annotated telemetry data

let params;  // form / URL params
let debug = 0;  // controls console logging

// URL-only parameters
let end_date_param;

// Extended telemetry URL params
let et_dec_param;
let et_labels_param;
let et_llabels_param;
let et_units_param;
let et_res_param;
let scaleVoltage_param;

let last_update_ts;
let next_update_ts;

let update_task;  // telemetry / map update task

// Last scroll position of the table / chart viewer
let last_data_view_scroll_pos = 0;

let is_mobile;  // running on a mobile device

// Notification support
let notifications_enabled = false;
let notification_permission_requested = false;

// WSPR band info. For each band, the value is
// [U4B starting minute offset, WSPR Live band id].
const kWSPRBandInfo = {
  '2200m': [0, -1],
  '630m': [4, 0],
  '160m': [8, 1],
  '80m': [2, 3],
  '60m': [6, 5],
  '40m': [0, 7],
  '30m': [4, 10],
  '20m': [8, 14],
  '17m': [2, 18],
  '15m': [6, 21],
  '12m': [0, 24],
  '10m': [4, 28],
  '6m': [8, 50],
  '4m': [2, 70],
  '2m': [6, 144],
  '70cm': [0, 432],
  '23cm': [4, 1296]
}

// Used for spot decoding
const kWSPRPowers = [0, 3, 7, 10, 13, 17, 20, 23, 27, 30, 33, 37, 40,
  43, 47, 50, 53, 57, 60];

// Adjust receiver coordinates to avoid long lines across the map
// when transmitter and receiver are on opposite sides of antimeridian
function adjustReceiverCoords(tx_lat_lng, rx_lat_lng) {
  const tx_lng = tx_lat_lng.lng;
  const rx_lng = rx_lat_lng.lng;

  // Calculate the difference in longitude
  const lng_diff = Math.abs(tx_lng - rx_lng);

  // If the difference is greater than 180°, we should go the other way
  if (lng_diff > 180) {
    let adjusted_rx_lng = rx_lng;

    // If transmitter is on the right side (positive longitude near +180)
    // and receiver is on the left side (negative longitude near -180)
    if (tx_lng > 0 && rx_lng < 0) {
      adjusted_rx_lng = rx_lng + 360;
    }
    // If transmitter is on the left side (negative longitude near -180)
    // and receiver is on the right side (positive longitude near +180)
    else if (tx_lng < 0 && rx_lng > 0) {
      adjusted_rx_lng = rx_lng - 360;
    }

    return L.latLng(rx_lat_lng.lat, adjusted_rx_lng);
  }

  // No adjustment needed
  return rx_lat_lng;
}

// Parses a UTC timestamp string like '2025-07-15 12:00:00' to a Date() object
function parseTimestamp(ts_str) {
  ts = new Date(Date.parse(ts_str.replace(' ', 'T') + 'Z'));
  if (!ts || isNaN(ts.getTime())) return null;
  return ts;
}

// Parses a string such as '2025-07-13' into a Date object or
// returns null if the string couldn't be parsed
function parseDate(date_str) {
  const date_regex = /^(\d{4})-(\d{1,2})-(\d{1,2})$/;
  const match = date_str.match(date_regex);
  if (!match) return null;
  const year = parseInt(match[1]);
  const month = parseInt(match[2]) - 1;  // 0-indexed
  const day = parseInt(match[3]);
  const date = new Date(Date.UTC(year, month, day));
  if (date.getUTCFullYear() !== year ||
    date.getUTCMonth() !== month ||
    date.getUTCDate() !== day) return null;
  return date;
}

// Formats a Date() object to a UTC string such as '2025-07-15 12:00:00'
function formatTimestamp(ts) {
  return ts.toISOString().slice(0, 16).replace('T', ' ');
}

// Extracts a parameter value from the URL
function getUrlParameter(name) {
  const regex = new RegExp('[?&]' + name + '(=([^&]*)|(?=[&]|$))');
  const match = regex.exec(location.search);
  if (!match) return null;
  return match[2] != undefined ?
    decodeURIComponent(match[2].replace(/\+/g, ' ')) : '';
}

// Parses and validates input params, returning them as a dictionary.
// Alerts the user and returns null if validation failed.
function parseParams() {
  const cs = document.getElementById('cs').value.trim().toUpperCase();
  const band = document.getElementById('band').value.trim();
  if (!(band in kWSPRBandInfo)) {
    alert('Invalid band');
    return null;
  }
  // Channel may also encode tracker type, such as Z4 for Zachtek
  const raw_ch = document.getElementById('ch').value.trim();
  let ch;
  let tracker;
  let fetch_et;
  const [starting_minute_offset, _] = kWSPRBandInfo[band];
  if (raw_ch.length > 1 && /^[A-Z]$/i.test(raw_ch[0])) {
    if (/[GZ]/i.test(raw_ch[0])) {
      // generic1 (g): unspecified protocol, single type 1 message
      // generic2 (G): unspecified protocol, type 2 + type 3 message combo
      // zachtek1 (z): older Zachtek protocol, single type 1 message
      // zachtek2 (Z): newer Zachtek protocol, type 2 + type 3 message combo
      tracker = {
        'g': 'generic1', 'G': 'generic2',
        'z': 'zachtek1', 'Z': 'zachtek2'
      }[raw_ch[0]];
      if (!/^[02468]$/.test(raw_ch.slice(1))) {
        alert('Starting minute should be one of 0, 2, 4, 6 or 8');
        return null;
      }
      // Convert channel to an equivalent u4b one
      ch = ((raw_ch[1] - '0' - starting_minute_offset) / 2 + 5) % 5;
    } else if (/[UW]/i.test(raw_ch[0])) {
      // Q34 format, where Q and 3 are special callsign ids and 4 is
      // the starting minute
      if (!/^[Q01][0-9][02468]$/i.test(raw_ch.slice(1))) {
        alert('Incorrect U/W channel format');
        return null;
      }
      // Convert channel to an equivalent u4b one
      ch = ['0', '1', 'Q'].indexOf(raw_ch[1]) * 200 +
        (raw_ch[2] - '0') * 20 +
        ((raw_ch[3] - '0' - starting_minute_offset) / 2 + 5) % 5;
      tracker = raw_ch[0].toUpperCase() == 'W' ? 'wb8elk' : 'u4b';
    } else {
      alert('Unknown tracker type: ' + raw_ch[0]);
      return null;
    }
  } else if (raw_ch == '') {
    // Showing regular callsign reports from all slots
    ch = 0;
    tracker = 'unknown';
  } else {
    // Default: U4B
    const match = raw_ch.match(/^(\d+)(E(\d*))?$/i);
    if (!match) {
      alert('Invalid U4B channel');
      return null;
    }
    ch = Number(match[1]);
    fetch_et = match[2] ? (match[3] ? Number(match[3]) : 1) : null;
    if (ch < 0 || ch > 599 ||
      (fetch_et != null &&
        (fetch_et < 0 || fetch_et > 3))) {
      alert('Invalid U4B channel');
      return null;
    }
    tracker = 'u4b';  // default
  }

  const start_date = parseDate(
    document.getElementById('start_date').value);
  const form_end_date = document.getElementById('end_date').value;
  const end_date = form_end_date ?
    parseDate(form_end_date) :
    (end_date_param ? parseDate(end_date_param) : new Date());
  const units = (units_param == null) ?
    (localStorage.getItem('units') == 1 ? 1 : 0) :
    (units_param == 'imperial' ? 1 : 0);
  const detail = localStorage.getItem('detail') == 1 ? 1 : 0;
  
  // For grid filtering, check the checkbox state if it exists, otherwise use localStorage
  const gridFilteringCheckbox = document.getElementById('enable_grid_filtering');
  const enable_grid_filtering = gridFilteringCheckbox ? 
    gridFilteringCheckbox.checked : 
    (localStorage.getItem('enable_grid_filtering') !== 'false'); // default true

  let cs_regex;
  if (['generic2', 'zachtek2', 'unknown'].includes(tracker)) {
    // Compound callsigns allowed
    cs_regex = /^([A-Z0-9]{1,4}\/)?[A-Z0-9]{4,6}(\/[A-Z0-9]{1,4})?$/i;
  } else {
    cs_regex = /^[A-Z0-9]{4,6}$/i;
  }
  if (!cs_regex.test(cs)) {
    alert('Please enter a valid callsign');
    return null;
  }

  if (!start_date) {
    alert('Start date should be in the YYYY-mm-dd format');
    return null;
  }

  if (!end_date) {
    alert('End date should be in the YYYY-mm-dd format');
    return null;
  }

  if (start_date > end_date) {
    alert('Start date should be before end date');
    return null;
  }

  if (end_date - start_date > 366 * 86400 * 1000) {
    alert('Start date cannot be more than a year before the end date. ' +
      'For past flights, end date can be specified with the ' +
      '&end_date=YYYY-mm-dd URL param');
    return null;
  }

  const et_spec = et_dec_param ? parseExtendedTelemetrySpec() : null;
  if (et_dec_param && !et_spec) {
    alert('Invalid ET spec');
    return null;
  }

  // Successful validation
  return {
    'cs': cs, 'ch': ch, 'band': band, 'tracker': tracker,
    'start_date': start_date, 'end_date': end_date,
    'fetch_et': fetch_et, 'units': units,
    'detail': detail, 'et_spec': et_spec, 'scaleVoltage': scaleVoltage_param
  };
}

// Helper function to check if grid filtering is enabled
function isGridFilteringEnabled() {
  const checkbox = document.getElementById('enable_grid_filtering');
  return checkbox ? checkbox.checked : true; // default true if checkbox not found
}

// Returns TX minute for given slot in the U4B protocol
function getU4BSlotMinute(slot) {
  const [starting_minute_offset, _] = kWSPRBandInfo[params.band];
  return (starting_minute_offset + ((params.ch % 5) + slot) * 2) % 10;
}

// Create a wspr.live SQL clause corresponding to desired date range
function createQueryDateRange(incremental_update = false) {
  if (incremental_update && last_update_ts) {
    // Fetch up to 6 hours prior to last update timestamp
    let cutoff_ts = new Date(last_update_ts);
    cutoff_ts.setHours(cutoff_ts.getHours() - 6);
    const cutoff_ts_str = formatTimestamp(cutoff_ts);
    return `time > '${cutoff_ts_str}:00'`;
  } else {
    const start_date = formatTimestamp(params.start_date).slice(0, 10);
    const end_date = formatTimestamp(params.end_date).slice(0, 10);
    return `time >= '${start_date}' AND time <= '${end_date} 23:58:00'`
  }
}

// Creates wspr.live query for fetching telemetry reports.
// Do not change this query unless you understand the impact
// on wpsr.live servers.
function createWSPRLiveQuery(
  fetch_q01 = false, slots = [0],
  incremental_update = false) {
  let cs_clause;
  if (fetch_q01) {
    // Fetching from the Q/0/1 callsign space
    if (params.tracker == 'u4b' || params.tracker == 'wb8elk') {
      const cs1 = ['0', '1', 'Q'][Math.floor(params.ch / 200)];
      const cs3 = Math.floor(params.ch / 20) % 10;
      cs_clause = `substr(tx_sign, 1, 1) = '${cs1}' AND ` +
        `substr(tx_sign, 3, 1) = '${cs3}'`;
    } else {
      throw new Error('Internal error');
    }
  } else {
    // Regular callsign query
    cs_clause = `tx_sign = '${params.cs}'`;
  }
  const [_, wspr_live_band] = kWSPRBandInfo[params.band];
  const slot_minutes = slots.map(slot => getU4BSlotMinute(slot));
  const slot_clause = slot_minutes.length < 5 ?
    `toMinute(time) % 10 IN (${slot_minutes})` : 'true';
  const date_range = createQueryDateRange(incremental_update);
  return `
    SELECT  /* wsprtv.github.io */
      time, tx_sign, tx_loc, power,
      groupArray(tuple(rx_sign, rx_loc, frequency, snr))
    FROM wspr.rx
    WHERE
      ${cs_clause} AND
      band = ${wspr_live_band} AND
      ${slot_clause} AND
      ${date_range}
    GROUP BY time, tx_sign, tx_loc, power
    FORMAT JSONCompact`;
}

// Executes a wspr.live query and returns the results as a JSON object
async function runQuery(query) {
  if (debug > 0) console.log(query);
  const encoded_query = encodeURIComponent(query);

  const url = `https://db1.wspr.live/?query=${encoded_query}`;
  const response = await fetch(url);
  if (!response.ok) throw new Error('HTTP error ' + response.status);
  return (await response.json()).data;
}

// Imports data from wspr.live for further processing:
// 1) Names the data members
// 2) Sorts rx reports by callsign
function importWSPRLiveData(data) {
  for (let i = 0; i < data.length; i++) {
    let row = data[i];
    data[i] = {
      'ts': parseTimestamp(row[0]),
      'cs': row[1], 'grid': row[2], 'power': row[3],
      'rx': row[4].map(
        rx => ({
          'cs': rx[0], 'grid': rx[1],
          'freq': rx[2], 'snr': rx[3]
        }))
        .sort((r1, r2) => (r1.cs > r2.cs) - (r1.cs < r2.cs))
    };
  }
  return data;
}

// Notification functions
async function requestNotificationPermission() {
  if (!('Notification' in window)) {
    console.log('This browser does not support notifications');
    return false;
  }

  if (Notification.permission === 'granted') {
    notifications_enabled = true;
    return true;
  }

  if (Notification.permission === 'denied') {
    return false;
  }

  // Request permission
  const permission = await Notification.requestPermission();
  notifications_enabled = (permission === 'granted');
  return notifications_enabled;
}

function showNewPacketNotification(new_count, callsign) {
  if (!notifications_enabled || !('Notification' in window)) {
    return;
  }

  const title = `New WSPR Packet${new_count > 1 ? 's' : ''}`;
  const body = `${new_count} new packet${new_count > 1 ? 's' : ''} received from ${callsign}`;

  const notification = new Notification(title, {
    body: body,
    icon: 'data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iMzIiIGhlaWdodD0iMzIiIHZpZXdCb3g9IjAgMCAzMiAzMiIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj4KICA8IS0tIEJhY2tncm91bmQgLS0+CiAgPHJlY3Qgd2lkdGg9IjMyIiBoZWlnaHQ9IjMyIiBmaWxsPSIjZmZmZmZmIi8+CiAgCiAgPCEtLSBNZXRlb3JvbG9naWNhbCBiYWxsb29uIChtYWluIHNwaGVyZSkgLS0+CiAgPGNpcmNsZSBjeD0iMTYiIGN5PSIxMiIgcj0iOCIgZmlsbD0iI2Y4ZjlmYSIgc3Ryb2tlPSIjMmQzNzQ4IiBzdHJva2Utd2lkdGg9IjEuNSIvPgogIAogIDwhLS0gQmFsbG9vbiBoaWdobGlnaHQgLS0+CiAgPGVsbGlwc2UgY3g9IjE0IiBjeT0iOSIgcng9IjIiIHJ5PSIzIiBmaWxsPSIjZmZmZmZmIiBvcGFjaXR5PSIwLjciLz4KICAKICA8IS0tIENvbm5lY3Rpb24gbGluZSBmcm9tIGJhbGxvb24gdG8gcGF5bG9hZCAtLT4KICA8bGluZSB4MT0iMTYiIHkxPSIyMCIgeDI9IjE2IiB5Mj0iMjUiIHN0cm9rZT0iIzJkMzc0OCIgc3Ryb2tlLXdpZHRoPSIxIi8+CiAgCiAgPCEtLSBQYXlsb2FkL2luc3RydW1lbnQgcGFja2FnZSAtLT4KICA8cmVjdCB4PSIxNCIgeT0iMjUiIHdpZHRoPSI0IiBoZWlnaHQ9IjMiIGZpbGw9IiMyZDM3NDgiIHJ4PSIwLjUiLz4KICAKICA8IS0tIFNtYWxsIGFudGVubmEgb24gcGF5bG9hZCAtLT4KICA8bGluZSB4MT0iMTYiIHkxPSIyNSIgeDI9IjE2IiB5Mj0iMjMiIHN0cm9rZT0iIzJkMzc0OCIgc3Ryb2tlLXdpZHRoPSIwLjUiLz4KPC9zdmc+Cg==',
    badge: 'data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iMzIiIGhlaWdodD0iMzIiIHZpZXdCb3g9IjAgMCAzMiAzMiIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj4KICA8IS0tIEJhY2tncm91bmQgLS0+CiAgPHJlY3Qgd2lkdGg9IjMyIiBoZWlnaHQ9IjMyIiBmaWxsPSIjZmZmZmZmIi8+CiAgCiAgPCEtLSBNZXRlb3JvbG9naWNhbCBiYWxsb29uIChtYWluIHNwaGVyZSkgLS0+CiAgPGNpcmNsZSBjeD0iMTYiIGN5PSIxMiIgcj0iOCIgZmlsbD0iI2Y4ZjlmYSIgc3Ryb2tlPSIjMmQzNzQ4IiBzdHJva2Utd2lkdGg9IjEuNSIvPgogIAogIDwhLS0gQmFsbG9vbiBoaWdobGlnaHQgLS0+CiAgPGVsbGlwc2UgY3g9IjE0IiBjeT0iOSIgcng9IjIiIHJ5PSIzIiBmaWxsPSIjZmZmZmZmIiBvcGFjaXR5PSIwLjciLz4KICAKICA8IS0tIENvbm5lY3Rpb24gbGluZSBmcm9tIGJhbGxvb24gdG8gcGF5bG9hZCAtLT4KICA8bGluZSB4MT0iMTYiIHkxPSIyMCIgeDI9IjE2IiB5Mj0iMjUiIHN0cm9rZT0iIzJkMzc0OCIgc3Ryb2tlLXdpZHRoPSIxIi8+CiAgCiAgPCEtLSBQYXlsb2FkL2luc3RydW1lbnQgcGFja2FnZSAtLT4KICA8cmVjdCB4PSIxNCIgeT0iMjUiIHdpZHRoPSI0IiBoZWlnaHQ9IjMiIGZpbGw9IiMyZDM3NDgiIHJ4PSIwLjUiLz4KICAKICA8IS0tIFNtYWxsIGFudGVubmEgb24gcGF5bG9hZCAtLT4KICA8bGluZSB4MT0iMTYiIHkxPSIyNSIgeDI9IjE2IiB5Mj0iMjMiIHN0cm9rZT0iIzJkMzc0OCIgc3Ryb2tlLXdpZHRoPSIwLjUiLz4KPC9zdmc+Cg==',
    tag: 'wspr-packet',
    requireInteraction: false,
    silent: false
  });

  // Auto-close after 4 seconds
  setTimeout(() => {
    notification.close();
  }, 4000);

  // Click handler to focus the window
  notification.onclick = function () {
    window.focus();
    notification.close();
  };
}

// Compares rows by (ts, cs)
function compareDataRows(r1, r2) {
  return r1.ts - r2.ts || (r1.cs > r2.cs) - (r1.cs < r2.cs);
}

// Both old_data and new_data are sorted by (row.ts, row.cs).
// Extends old_data with items in new_data whose keys are not
// present in old_data and returns the result.
// Returns {data: merged_data, new_count: number_of_new_items}
function mergeData(old_data, new_data) {
  let result = [];
  let i = 0;  // index in old_data
  let j = 0;  // index in new_data
  let new_count = 0;  // count of truly new items

  while (i < old_data.length && j < new_data.length) {
    let cmp = compareDataRows(old_data[i], new_data[j]);
    if (cmp < 0) {
      result.push(old_data[i++]);
    } else if (cmp > 0) {
      result.push(new_data[j++]);
      new_count++;
    } else {
      // Prefer new_data -- it is more complete
      result.push(new_data[j++]);
      i++;
    }
  }

  // Append remaining elements, if any
  while (i < old_data.length) result.push(old_data[i++]);
  while (j < new_data.length) {
    result.push(new_data[j++]);
    new_count++;
  }

  return { data: result, new_count: new_count };
}

// Given two sets of sorted RX reports, check if any callsign
// is in both, and the RX frequency is similar
function findCoreceiver(rx1, rx2) {
  let i = 0;  // index in rx1
  let j = 0;  // index in rx2
  for (; ;) {
    if (i >= rx1.length || j >= rx2.length) return false;
    const r1 = rx1[i];
    const r2 = rx2[j];
    if (r1.cs == r2.cs) {
      if (Math.abs(r1.freq - r2.freq) <= 5) return true;
      i++;
      j++;
    } else if (r1.cs < r2.cs) {
      i++;
    } else {
      j++;
    }
  }
}

// Combines telemetry data from corresponding WSPR messages (regular callsign +
// basic telemetry messages for U4B, type 2 and type 3 for Zachtek).
// Returns a list of spots, with each spot having one or more messages
// attached.
function matchTelemetry(data) {
  try {
    let spots = [];

    let starting_minute = getU4BSlotMinute(0);
    let last_spot;

    for (let i = 0; i < data.length; i++) {
      row = data[i];
      if (params.tracker == 'unknown') {
        spots.push({ 'slots': [row] });
        continue;
      }
      const slot = (((row.ts.getMinutes() - starting_minute) + 10) % 10) / 2;
      if (slot == 0) {
        if (!last_spot || last_spot.slots[0].ts != row.ts) {
          // New spot
          last_spot = { 'slots': [row] };
          spots.push(last_spot);
        }
      } else if (last_spot && row.ts - last_spot.slots[0].ts < 10 * 60 * 1000 &&
        !last_spot.slots[slot]) {
        // Same TX sequence as last spot, try to attach the row
        if (params.tracker == 'zachtek2' || params.tracker == 'generic2') {
          // Always a match
          last_spot.slots[slot] = row;
        } else if (params.tracker == 'wb8elk') {
          if (last_spot.slots[0].grid == row.grid) {
            last_spot.slots[slot] = row;
          }
        } else if (params.tracker == 'u4b') {
          // U4B frequency matching - but also allow matching based on timestamp proximity
          let matched = false;
          
          // First try frequency matching with existing slots
          for (let j = 0; j < slot; j++) {
            if (last_spot.slots[j] &&
              findCoreceiver(last_spot.slots[j].rx, row.rx)) {
              last_spot.slots[slot] = row;
              matched = true;
              break;
            }
          }
          
          // If frequency matching failed, but we're within a reasonable time window
          // and this looks like extended telemetry, allow the match
          if (!matched && slot >= 2 && row.cs && row.cs.length === 6) {
            try {
              const [m, n] = extractU4BQ01Payload(row);
              if (!(n % 2)) { // This is extended telemetry (even n)
                // Allow the match based on timing alone for extended telemetry
                last_spot.slots[slot] = row;
                matched = true;
              }
            } catch (e) {
              // If extraction fails, don't match
            }
          }
        }
      }
    }
    return spots;
  } catch (error) {
    console.error('Error in matchTelemetry:', error);
    throw error;
  }
}

// Convert a Maidenhead grid reference of arbitrary previcision to lat/long.
function maidenheadToLatLon(grid) {
  // Make sure we are in upper case so our maths works. Case is arbitrary for Maidenhead references
  grid = grid.toUpperCase();

  // Return null if our Maidenhead string is invalid or too short
  let len = grid.length;
  if (len <= 0 || (len % 2) !== 0) {
    return null;
  }

  let lat = 0.0; // aggregated latitude
  let lon = 0.0; // aggregated longitude
  let latCellSize = 10; // Size in degrees latitude of the current cell. Starts at 20 and gets smaller as the calculation progresses
  let lonCellSize = 20; // Size in degrees longitude of the current cell. Starts at 20 and gets smaller as the calculation progresses
  let latCellNo; // grid latitude cell number this time
  let lonCellNo; // grid longitude cell number this time

  // Iterate through blocks (two-character sections)
  for (let block = 0; block * 2 < len; block += 1) {
    if (block % 2 === 0) {
      // Letters in this block
      lonCellNo = grid.charCodeAt(block * 2) - 'A'.charCodeAt(0);
      latCellNo = grid.charCodeAt(block * 2 + 1) - 'A'.charCodeAt(0);
    } else {
      // Numbers in this block
      lonCellNo = parseInt(grid.charAt(block * 2));
      latCellNo = parseInt(grid.charAt(block * 2 + 1));
    }

    // Aggregate the angles
    lat += latCellNo * latCellSize;
    lon += lonCellNo * lonCellSize;

    // Reduce the cell size for the next block, unless we are on the last cell. If we are on the last cell, instead
    // move the position into the middle of the cell rather than its south-west corner.
    if (block * 2 < len - 2) {
      // Still have more work to do, so reduce the cell size
      if (block % 2 === 0) {
        // Just dealt with letters, next block will be numbers so cells will be 1/10 the current size
        latCellSize = latCellSize / 10.0;
        lonCellSize = lonCellSize / 10.0;
      } else {
        // Just dealt with numbers, next block will be letters so cells will be 1/24 the current size
        latCellSize = latCellSize / 24.0;
        lonCellSize = lonCellSize / 24.0;
      }
    } else {
      // This is the last block, so move the marker to the middle.
      lat += latCellSize / 2;
      lon += lonCellSize / 2;
    }
  }

  // Offset back to (-180, -90) where the grid starts
  lon -= 180.0;
  lat -= 90.0;

  return [lat, lon];
}

// Returns c's offset in ['A'..'Z'] if alphanum is false and in
// [0..9A..Z] otherwise
function charToNum(c, alphanum = false) {
  let code = c.charCodeAt(0);
  let A = 'A'.charCodeAt(0);
  if (alphanum) {
    if (code >= A) {
      return code - A + 10;
    } else {
      let zero = '0'.charCodeAt(0);
      return code - zero;
    }
  } else {
    return code - A;
  }
}

// Given a Q01 message, extracts m and n values from
// callsign and (grid, power) respectively
function extractU4BQ01Payload(p) {
  let m = ((((charToNum(p.cs[1], true) * 26 + charToNum(p.cs[3])) * 26) +
    charToNum(p.cs[4]))) * 26 + charToNum(p.cs[5]);
  let n = ((((charToNum(p.grid[0]) * 18 + charToNum(p.grid[1])) * 10) +
    charToNum(p.grid[2], true)) * 10 + charToNum(p.grid[3], true)) * 19 +
    kWSPRPowers.indexOf(p.power);
  return [m, n];
}

// Decode enhanced grid square from extended telemetry location value
function decodeEnhancedGridFromET(locValue, baseGrid) {
  if (locValue === undefined || locValue === null || !baseGrid) return null;

  // The Loc field contains a numeric value representing the 7th and 8th characters
  // of an 8-character grid square (grid78)

  let value = Math.floor(locValue);
  if (value < 0 || value >= 100) return null; // 10*10 = 100 possible combinations (0-9 each)

  // Convert numeric value to 7th and 8th grid characters
  // Grid characters 7&8 are numbers 0-9 representing extended square precision
  let char8 = value % 10;  // 8th character (latitude extended square)
  let char7 = Math.floor(value / 10) % 10;  // 7th character (longitude extended square)

  // Convert to number characters
  let grid7 = char7.toString();  // 0-9
  let grid8 = char8.toString();  // 0-9

  // Build 8-character grid square by adding the 7th and 8th characters
  // to the existing 6-character grid
  // Only add grid78 if we already have a proper 6-character grid (grid56 present)
  if (baseGrid.length >= 6) {
    return baseGrid + grid7 + grid8;
  }

  // Don't add grid78 if we only have a 4-character grid
  // (grid56 characters haven't been added yet)
  return null;
}

function processU4BSlot1Message(spot) {
  if (spot.slots[1].cs.length != 6) {
    return false;
  }
  // Extract values from callsign
  const [m, n] = extractU4BQ01Payload(spot.slots[1]);
  if (!(n % 2)) {
    if (params.fetch_et == 0) {
      // Possible extended telemetry in slot1
      return processU4BExtendedTelemetryMessage(spot, 1);
    }
    return false;
  }
  let p = Math.floor(m / 1068);
  let grid = spot.grid + String.fromCharCode(97 + Math.floor(p / 24)) +
    String.fromCharCode(97 + (p % 24));
  let altitude = (m % 1068) * 20;

  if (!(Math.floor(n / 2) % 2)) {
    // Invalid GPS bit
    return false;
  }
  // Fill values
  spot.speed = (Math.floor(n / 4) % 42) * 2 * 1.852;
  let voltage = ((Math.floor(n / 168) + 20) % 40) * 0.05 + 3;
  if (params.scaleVoltage) {
    voltage -= 2;
  }
  spot.voltage = voltage;
  spot.temp = (Math.floor(n / 6720) % 90) - 50;
  spot.grid = grid;
  spot.altitude = altitude;
  return true;
}

function processU4BExtendedTelemetryMessage(spot, i) {
  const [m, n] = extractU4BQ01Payload(spot.slots[i]);
  if (n % 2) {
    // Not an extended telemetry message
    return false;
  }
  const v = Math.floor((m * 615600 + n) / 2);
  if (!spot.raw_et) {
    spot.raw_et = [];
  }
  spot.raw_et[i] = v;
  return true;
}

function processWB8ELKSlot1Message(spot) {
  if (spot.slots[1].cs.length != 6) {
    return false;
  }
  spot.altitude += 60 * kWSPRPowers.indexOf(spot.slots[1].power);
  let grid = spot.slots[1].grid.slice(0, 4);
  if (spot.grid != grid ||
    !/^[A-X][A-X]$/.test(spot.slots[1].cs.slice(4))) {
    return false;
  }
  spot.grid += spot.slots[1].cs.slice(4, 6).toLowerCase();
  spot.voltage =
    3.3 + (spot.slots[1].cs.charCodeAt(3) - 'A'.charCodeAt(0)) * 0.1;
  return true;
}

// Annotates telemetry spots (appends lat, lon, speed, etc)
function decodeSpots() {
  try {
    spots = spots.filter(spot => decodeSpot(spot));
  } catch (error) {
    console.error('Error in decodeSpots:', error);
    throw error;
  }
}

// Decodes and annotates a spot
// as documented at https://qrp-labs.com/flights/s4.html.
// Note: voltage calculation is documented incorrectly there.
function decodeSpot(spot) {
  spot.ts = spot.slots[0].ts;
  spot.grid = (params.tracker == 'unknown') ?
    spot.slots[0].grid : spot.slots[0].grid.slice(0, 4);
  if (params.tracker == 'wb8elk') {
    spot.altitude = 1000 * kWSPRPowers.indexOf(spot.slots[0].power);
    if (spot.slots[1]) {
      if (!processWB8ELKSlot1Message(spot)) {
        spot.slots[1].is_invalid = true;
      }
    }
  } else if (params.tracker == 'zachtek1') {
    spot.altitude = spot.slots[0].power * 300;
  } else if (params.tracker == 'generic1') {
    // Nothing to do here
  } else if (params.tracker == 'zachtek2' || params.tracker == 'generic2') {
    if (!spot.slots[1]) {
      // Slot 1 need to be present as it contains the location. WSPRNet
      // guesses the location for type 2 (slot 0) messages. Relying
      // just on type 3 (slot 1) messages risks 15-bit hash collisions.
      return false;
    }
    if (params.tracker == 'zachtek2') {
      spot.altitude = spot.slots[0].power * 300 + spot.slots[1].power * 20;
    }
    // Grid comes from slot1 (type 3) message
    spot.grid = spot.slots[1].grid;
  } else if (params.tracker == 'u4b') {
    // Default: U4B
    if (spot.slots[1]) {
      if (!processU4BSlot1Message(spot)) {
        spot.slots[1].is_invalid = true;
      }
    }
    // Process extended telemetry, if any
    for (let i = 2; i < spot.slots.length; i++) {
      if (spot.slots[i] && !processU4BExtendedTelemetryMessage(spot, i)) {
        spot.slots[i].is_invalid = true;
        return true;
      }
    }
  }
  [spot.lat, spot.lon] = maidenheadToLatLon(spot.grid);
  if (spot.raw_et) {
    decodeExtendedTelemetry(spot);
    // Use enhanced location from extended telemetry if available
    // The "Loc" field is at index 1 in the extended telemetry data
    if (spot.et && spot.et[1] !== undefined) {
      const enhancedGrid = decodeEnhancedGridFromET(spot.et[1], spot.grid);
      if (enhancedGrid) {
        spot.grid = enhancedGrid;
        [spot.lat, spot.lon] = maidenheadToLatLon(enhancedGrid);
      }
    }
  }
  return true;
}

function decodeExtendedTelemetry(spot) {
  if (!params.et_spec || !spot.raw_et) return null;
  let et = [];
  let index = 0;  // index within data
  let ts_seq = spot.ts.getUTCHours() * 30 + spot.ts.getUTCMinutes() / 2;
  for (let i = 0; i < spot.raw_et.length; i++) {
    const raw_et = spot.raw_et[i];
    if (raw_et == undefined) continue;
    const decoders = params.et_spec.decoders;
    for (let j = 0; j < decoders.length; j++) {
      const [filters, extractors] = decoders[j];
      let matched = true;
      for (let filter of filters) {
        if (filter.length == 4 && filter[0] == 't' &&
          Math.trunc(ts_seq / filter[1]) % filter[2] != filter[3]) {
          matched = false;
          break;
        }
        if (filter.length == 2 && filter[0] == 's' &&
          filter[1] != i) {
          matched = false;
          break;
        }
        if (filter.length != 3) continue;
        let [divisor, modulus, expected_value] = filter;
        if (expected_value == 's') expected_value = i; // slot
        if (Math.trunc(raw_et / divisor) % modulus != expected_value) {
          matched = false;
          break;
        }
      }
      if (matched) {
        // Extract the values
        for (const [divisor, modulus, offset, slope] of extractors) {
          et[index++] = offset +
            (Math.trunc(raw_et / divisor) % modulus) * slope;
        }
        break;  // do not try other decoders
      } else {
        // Skip over the missing indices
        index += extractors.length;
      }
    }
  }
  if (et) spot.et = et;
  return data;
}

// Value formatting

function formatDuration(ts1, ts2) {
  const delta = Math.abs(ts1 - ts2) / 1000;
  const days = Math.floor(delta / 86400);
  const hours = Math.floor((delta % 86400) / 3600);
  const mins = Math.floor((delta % 3600) / 60);
  if (delta >= 86400) {
    return `${days}d ${hours}h`;
  } else if (delta >= 3600) {
    return `${hours}h ${mins}m`;
  } else {
    return `${mins}m`;
  }
}

function formatDistance(m, append_units = true) {
  const v = getDistanceInCurrentUnits(m);
  const [units, _] = kUnitInfo['distance'][params.units]
  return v + (append_units ? units : '');
}

function formatSpeed(kph, append_units = true) {
  const v = getSpeedInCurrentUnits(kph);
  const [units, _] = kUnitInfo['speed'][params.units];
  return v + (append_units ? units : '');
}

// Vertical speed, mpm = m/min
function formatVSpeed(mpm, append_units = true) {
  const v = getVSpeedInCurrentUnits(mpm);
  const [units, _] = kUnitInfo['vspeed'][params.units];
  return v + (append_units ? units : '');
}

function formatAltitude(m, append_units = true) {
  const v = getAltitudeInCurrentUnits(m);
  const [units, resolution] = kUnitInfo['altitude'][params.units];
  return (resolution ? v.toFixed(resolution) : v) +
    (append_units ? units : '');
}

function formatTemperature(c, append_units = true) {
  const v = getTemperatureInCurrentUnits(c);
  const [units, _] = kUnitInfo['temp'][params.units]
  return v + (append_units ? units : '');
}

function formatVoltage(v, append_units = true) {
  return v.toFixed(2) + (append_units ? 'V' : '');
}

function getDistanceInCurrentUnits(m) {
  return (params.units == 0) ?
    Math.round(m / 1000) :
    Math.round(m * 0.621371 / 1000);
}

function getAltitudeInCurrentUnits(m) {
  return (params.units == 0) ?
    m / 1000 : Math.round(m * 3.28084 / 10) * 10;
}

function getSpeedInCurrentUnits(kph) {
  return (params.units == 0) ?
    Math.round(kph) : Math.round(kph * 0.621371);
}

function getVSpeedInCurrentUnits(mpm) {
  return (params.units == 0) ?
    Math.round(mpm) : Math.round(mpm * 3.28084);
}

function getTemperatureInCurrentUnits(c) {
  return (params.units == 0) ?
    Math.round(c) : Math.round(c * 9 / 5 + 32);
}

function getSunElevation(ts, lat, lon) {
  const sun_pos = SunCalc.getPosition(ts, lat, lon);
  return Math.round(sun_pos.altitude * 180 / Math.PI);
}

function getTimeSinceSunrise(ts, lat, lon) {
  return ts - SunCalc.getTimes(ts, lat, lon).sunrise;
}

function getTimeToSunset(ts, lat, lon) {
  return SunCalc.getTimes(ts, lat, lon).sunset - ts;
}

// Returns [num_rx, max_rx_dist, max_snr]
function getRXStats(spot) {
  let cs = {};
  let grids = {};
  let max_snr = -100;
  for (let i = 0; i < spot.slots.length; i++) {
    const slot = spot.slots[i];
    if (slot) {
      for (let j = 0; j < slot.rx.length; j++) {
        const rx = slot.rx[j];
        max_snr = Math.max(max_snr, rx.snr);
        cs[rx.cs] = 1;
        grids[rx.grid] = 1;
      }
    }
  }
  
  // Handle orphaned spots that don't have lat/lon
  let max_rx_dist = 0;
  if (spot.lat !== undefined && spot.lat !== null && 
      spot.lon !== undefined && spot.lon !== null && 
      Object.keys(grids).length > 0) {
    const lat_lon = L.latLng([spot.lat, spot.lon]);
    max_rx_dist = Math.max(...Object.keys(grids).map(grid =>
      lat_lon.distanceTo(maidenheadToLatLon(grid))));
  }
  
  return [Object.keys(cs).length, max_rx_dist, max_snr];
}

// Units / localization

// Metric / imperial, with second param being the display resolution.
// Spaces in units are deliberate: 5 mph vs 5V.
const kUnitInfo = {
  'speed': [[' km/h', 0], [' mph', 0]],
  'vspeed': [[' m/min', 0], [' ft/min', 0]],
  'altitude': [[' km', 2], [' ft', 0]],
  'distance': [[' km', 0], [' mi', 0]],
  'temp': [['°C', 0], ['°F', 1]],
  'voltage': [['V', 2], ['V', 2]],
  'power': [[' dBm', 0], [' dBm', 0]],
  'snr': [[' dB', 0], [' dB', 0]],
  'angle': [['°', 0], ['°', 0]],
};

function toggleUnits() {
  params.units ^= 1;

  // Always redraw both the track and data view since they're both visible
  displayTrack();

  // Remember units preference
  localStorage.setItem('units', params.units);
}

// Only count distance between points at least 100km apart.
// This improves accuracy when there are zig-zags.
function computeDistance(markers) {
  if (!markers) return 0;
  let dist = 0;
  let last_marker = markers[0];
  for (let i = 1; i < markers.length; i++) {
    const segment_dist = markers[i].getLatLng().distanceTo(
      last_marker.getLatLng());
    if (segment_dist > 100000 || i == markers.length - 1) {
      dist += segment_dist;
      last_marker = markers[i];
    }
  }
  return dist;
}

// Removes all existing markers and segments from the map
function clearTrack() {
  if (marker_group) {
    marker_group.clearLayers();
    segment_group.clearLayers();
    map.removeLayer(marker_group);
    map.removeLayer(segment_group);
    markers = [];
    marker_group = null;
    segment_group = null;
  }
  document.getElementById('spot_info').style.display = 'none';
  document.getElementById('synopsis').innerHTML = '';
  document.getElementById('update_countdown').innerHTML = '';
  document.getElementById('aux_info').style.display = 'none';
  if (selected_marker) {
    hideMarkerRXInfo(selected_marker);
  }
  selected_marker = null;
  last_marker = null;
}

// Draws the track on the map
function displayTrack() {
  try {
    clearTrack();
    marker_group = L.featureGroup();
    segment_group = L.featureGroup();

    // To reduce clutter, we only show grid4 markers if they are more than
    // 200km and/or 2 hours from adjacent grid6 markers. In other words, we only
    // display grid4 markers if there are no good adjacent grid6 markers to show
    // instead.
    for (let i = 0; i < spots.length; i++) {
      let spot = spots[i];
      if (spot.lat == undefined || spot.lon == undefined) continue;

      if (spot.cspeed && spot.cspeed > 300) {
        // Spot is too far from previous marker to be feasible (over 300 km/h
        // speed needed to connect). Ignore.
        if (debug > 0) console.log('Filtering out an impossible spot');
        continue;
      }

    let marker = null;
    if (spot.grid.length < 6) {
      // Grid4 spot
      if (!isGridFilteringEnabled() || params.tracker == 'unknown' || !last_marker ||
        (spot.ts - last_marker.spot.ts > 2 * 3600 * 1000) ||
        (last_marker.getLatLng().distanceTo(
          [spot.lat, spot.lon]) > 200000)) {
        marker = L.circleMarker([spot.lat, spot.lon],
          {
            radius: 4, color: 'black', fillColor: 'white', weight: 1,
            stroke: true, fillOpacity: 1
          });
      }
    } else if (spot.grid.length == 6) {
      // Grid6 spot
      if (isGridFilteringEnabled() && params.tracker != 'unknown' &&
        last_marker && last_marker.spot.grid.length < 6 &&
        (spot.ts - last_marker.spot.ts < 2 * 3600 * 1000) &&
        (last_marker.getLatLng().distanceTo(
          [spot.lat, spot.lon]) < 200000)) {
        // Remove last grid4 marker
        if (debug > 0) console.log('Removing grid4 marker due to grid6 spot');
        marker_group.removeLayer(last_marker);
        markers.pop();
      }
      marker = L.circleMarker([spot.lat, spot.lon],
        {
          radius: 5, color: 'black', fillColor: '#add8e6', weight: 1,
          stroke: true, fillOpacity: 1
        });
    } else if (spot.grid.length == 8) {
      // Grid8 spot - only display if we already have a grid6 marker
      if (isGridFilteringEnabled() && params.tracker != 'unknown' &&
        last_marker && last_marker.spot.grid.length < 8 &&
        (spot.ts - last_marker.spot.ts < 2 * 3600 * 1000) &&
        (last_marker.getLatLng().distanceTo(
          [spot.lat, spot.lon]) < 200000)) {
        // Remove last lower-precision marker
        if (debug > 0) console.log('Removing lower precision marker due to grid8 spot');
        marker_group.removeLayer(last_marker);
        markers.pop();
      }
      marker = L.circleMarker([spot.lat, spot.lon],
        {
          radius: 7, color: 'black', fillColor: '#87ceeb', weight: 1,
          stroke: true, fillOpacity: 1
        });
    }
    if (marker) {
      last_marker = marker;
      marker.spot = spot;
      marker.addTo(marker_group);
      markers.push(marker);
    }
  }

  // Highlight the first and last marker
  if (markers.length > 0) {
    markers[0].setStyle({ fillColor: '#3cb371' });
  }
  if (last_marker) {
    last_marker.setStyle({ fillColor: 'red' });
  }

  // Populate flight synopsis
  let synopsis = document.getElementById('synopsis');
  if (markers.length > 0) {
    const last_spot = last_marker.spot;
    const duration = formatDuration(last_marker.spot.ts, markers[0].spot.ts);
    synopsis.innerHTML = `Duration: <b>${duration}</b>`;
    if (params.tracker != 'unknown') {
      // Distance is a clickable link to switch units
      const dist = computeDistance(markers);
      synopsis.innerHTML += ' • Distance: <b>' +
        '<a href="#" id="unit_switch_link" title="Click to change units" ' +
        'onclick="toggleUnits(); event.preventDefault()">' +
        formatDistance(dist) + '</a></b>';
    }
    synopsis.innerHTML += ` • <b>${markers.length}</b> map spot` +
      ((markers.length > 1) ? 's' : '');
    if ('altitude' in last_spot) {
      synopsis.innerHTML += ' • Last altitude: <b>' +
        formatAltitude(last_spot.altitude) + '</b>';
    }
    if ('speed' in last_spot) {
      synopsis.innerHTML +=
        ` • Last speed: <b>${formatSpeed(last_spot.speed)}</b>`;
    }
    if ('voltage' in last_spot) {
      synopsis.innerHTML +=
        ` • Last voltage: <b>${formatVoltage(last_spot.voltage)}</b>`;
    }
    const last_age = formatDuration(new Date(), last_spot.ts);
    synopsis.innerHTML += ` • <b>(<span id='last_age'>${last_age}` +
      `</span> ago)</b>`;
  } else {
    synopsis.innerHTML = '<b>0</b> spots';
  }

  displayNextUpdateCountdown();

  // Add segments between markers
  // Handle segments across map edges
  for (let i = 1; i < markers.length; i++) {
    if (params.tracker == 'unknown') {
      // Do not draw lines between markers for 'unknown' trackers
      continue;
    }
    let lat1 = markers[i - 1].getLatLng().lat;
    let lon1 = markers[i - 1].getLatLng().lng;
    let lat2 = markers[i].getLatLng().lat;
    let lon2 = markers[i].getLatLng().lng;

    if (lon1 < lon2) {
      // Reorder so that lon1 is east of lon2 when crossing the antimeridian
      [[lat1, lon1], [lat2, lon2]] = [[lat2, lon2], [lat1, lon1]];
    }
    if (lon1 - lon2 > 180) {
      // The segment crosses the antimeridian (lon=180 line). Leaflet doesn't
      // display these correctly. Instead, we will display 2 segments -- from
      // marker1 to antimeridian and from antimeridian to marker2. For this to
      // work, the latitude at which the segment crosses antimeridian needs to
      // be calculated.
      let lat180 = lat1 + (lat2 - lat1) * (180 - lon1) /
        (lon2 - lon1 + 360);
      L.polyline([[lat1, lon1], [lat180, 180]],
        { color: '#00cc00' }).addTo(segment_group);
      L.polyline([[lat2, lon2], [lat180, -180]],
        { color: '#00cc00' }).addTo(segment_group);
    } else {
      // Regular segment, no antimeridian crossing
      L.polyline(
        [markers[i - 1].getLatLng(), markers[i].getLatLng()],
        { color: '#00cc00' }).addTo(segment_group);
    }
  }

  segment_group.addTo(map);
  marker_group.addTo(map);

  if (spots && spots.length > 0) {
    // Automatically show the data view after displaying the track
    showDataView();
  }

  marker_group.on('mouseover', onMarkerMouseover);
  marker_group.on('mouseout', onMarkerMouseout);
  marker_group.on('click', onMarkerClick);
  } catch (error) {
    console.error('Error in displayTrack:', error);
    throw error;
  }
}

function onMarkerMouseover(e) {
  let marker = e.layer;
  if (selected_marker && selected_marker != marker) {
    hideMarkerRXInfo(selected_marker);
    selected_marker = null;
  }
  displaySpotInfo(marker, e.containerPoint);
}

function onMarkerMouseout(e) {
  let marker = e.layer;
  if (marker != selected_marker) {
    let spot_info = document.getElementById('spot_info');
    spot_info.style.display = 'none';
  }
}

function onMarkerClick(e) {
  let marker = e.layer;
  const spot = marker.spot;

  // Hide any previously displayed receivers
  if (marker_with_receivers) {
    hideMarkerRXInfo(marker_with_receivers);
  }

  // Hide any previously selected marker's receiver info
  if (selected_marker) {
    hideMarkerRXInfo(selected_marker);
  }

  // Show receivers for the clicked marker, but don't make it "selected"
  // This allows the info to hide on mouseout like normal hover behavior
  marker.rx_markers = [];
  marker.rx_segments = [];
  spot.slots[0].rx.forEach(r => {
    let rx_lat_lon = maidenheadToLatLon(r.grid);

    // Adjust receiver coordinates to avoid long lines across the map
    let adjusted_rx_lat_lon = adjustReceiverCoords(marker.getLatLng(), L.latLng(rx_lat_lon));

    let rx_marker = L.circleMarker(
      adjusted_rx_lat_lon,
      {
        radius: 6, color: 'black',
        fillColor: 'yellow', weight: 1, stroke: true,
        fillOpacity: 1
      }).addTo(map);
    rx_marker.on('click', function (e) {
      L.DomEvent.stopPropagation(e);
    });
    let dist = marker.getLatLng().distanceTo(rx_lat_lon);
    rx_marker.bindTooltip(
      `${r.cs} ${formatDistance(dist)} ${r.snr} dBm`,
      { direction: 'top', opacity: 0.8 });
    marker.rx_markers.push(rx_marker);

    let segment = L.polyline([marker.getLatLng(), adjusted_rx_lat_lon],
      { weight: 1.4, color: 'blue' }).addTo(map).bringToBack();
    marker.rx_segments.push(segment);
  });

  // Track which marker has receivers displayed and clear selected marker
  marker_with_receivers = marker;
  selected_marker = null;

  L.DomEvent.stopPropagation(e);
}

function onMapClick(e) {
  // Hide spot info if currently displayed
  document.getElementById('spot_info').style.display = 'none';

  // Hide any receivers that are currently displayed
  if (marker_with_receivers) {
    hideMarkerRXInfo(marker_with_receivers);
    marker_with_receivers = null;
  }

  // Display lat / lng / sun elevation of clicked point
  const lat = e.latlng.lat.toFixed(2);
  const lon = e.latlng.lng.toFixed(2);

  const now = new Date();

  const sun_pos = SunCalc.getPosition(now, lat, lon);
  const sun_elev = Math.round(sun_pos.altitude * 180 / Math.PI);

  const hrs_sunrise = (getTimeSinceSunrise(now, lat, lon) / 3600000).toFixed(1);
  const hrs_sunset = (getTimeToSunset(now, lat, lon) / 3600000).toFixed(1);

  // Update the display
  let aux_info = document.getElementById('aux_info');
  aux_info.innerHTML = `${lat}, ${lon} | ${sun_elev}&deg; `;
  if (!isNaN(hrs_sunrise)) {
    aux_info.innerHTML += `/ ${hrs_sunrise} / ${hrs_sunset} hr`;
  }

  if (selected_marker) {
    // Display distance to the previously clicked marker
    let dist = e.latlng.distanceTo(selected_marker.getLatLng());
    aux_info.innerHTML += ' | ' + formatDistance(dist);
    // Clicking anywhere on the map hides the info bar for the last
    // clicked marker
    hideMarkerRXInfo(selected_marker);
    selected_marker = null;
  }
  aux_info.style.display = 'block';
}

function hideMarkerRXInfo(marker) {
  if (marker.rx_markers) {
    marker.rx_markers.forEach(rx_marker => map.removeLayer(rx_marker));
    delete marker.rx_markers;
    marker.rx_segments.forEach(rx_segment => map.removeLayer(rx_segment));
    delete marker.rx_segments;
  }
}

function displaySpotInfo(marker, point) {
  let spot = marker.spot;
  let spot_info = document.getElementById('spot_info');
  spot_info.style.left = point.x + 50 + 'px';
  spot_info.style.top = point.y - 20 + 'px';
  const utc_ts = formatTimestamp(spot.ts);
  spot_info.innerHTML = `<span style="color: #ffc">${utc_ts} UTC</span>`;
  for (let i = 0; i < spot.slots.length; i++) {
    const slot = spot.slots[i];
    if (slot && !slot.is_invalid) {
      spot_info.innerHTML +=
        `<br>${i}: ${slot.cs} ${slot.grid} ${slot.power}`;
    }
  }
  spot_info.innerHTML +=
    `<br>Grid: ${spot.grid || 'Unknown'}`;
  spot_info.innerHTML +=
    `<br>Coords: ${spot.lat.toFixed(6)}°, ${spot.lon.toFixed(6)}°`;
  if ('altitude' in spot) {
    spot_info.innerHTML += '<br>Altitude: ' + formatAltitude(spot.altitude);
  }
  if ('speed' in spot) {
    spot_info.innerHTML += `<br>Speed: ${formatSpeed(spot.speed)}`;
  }
  if ('temp' in spot) {
    spot_info.innerHTML += `<br>Temp: ${formatTemperature(spot.temp)}`;
  }
  if ('voltage' in spot) {
    spot_info.innerHTML += `<br>Voltage: ${formatVoltage(spot.voltage)}`;
  }
  if (spot.raw_et) {
    // Display opaque extended telemetry
    spot.raw_et.forEach((v, i) =>
      spot_info.innerHTML += `<br>Raw ET${i}: ${v}`);
  }
  if (spot.et) {
    // Display decoded extended telemetry
    let count = 0;
    spot.et.forEach((v, i) => {
      if (count++ < 8) {
        const [label, long_label, units, formatter] =
          getExtendedTelemetryAttributes(i);
        spot_info.innerHTML += `<br>${label}: ${formatter(v, true)}`
      }
    });
  }
  const sun_elev = getSunElevation(spot.ts, spot.lat, spot.lon);
  spot_info.innerHTML += `<br>Sun elevation: ${sun_elev}&deg;`
  const [num_rx, max_rx_dist, max_snr] = getRXStats(spot);
  spot_info.innerHTML += `<br> ${num_rx} report` +
    ((num_rx == 1) ? '' : 's');
  spot_info.innerHTML += ` | ${max_snr} dBm`;
  spot_info.innerHTML += `<br> ${formatDistance(max_rx_dist)}`;

  if (marker == selected_marker) {
    // Add GoogleEarth view
    const d = spot.altitude / 0.23075;
    const dl = d / (111320 * Math.cos(spot.lat * 0.01745));
    const dt = Math.round((spot.altitude ** 2 + d ** 2) ** 0.5);
    spot_info.innerHTML +=
      '<br><br><a href="https://earth.google.com/web/@' +
      spot.lat.toFixed(3) + ',' +
      (spot.lon + dl).toFixed(3) + ',0a,' +
      dt + 'd,35y,90h,77t" ' +
      'style="color: white;" target=new>GoogleEarth View</a>' +
      '<br>(use CTRL-arrows<br>to look around)';
  }

  spot_info.style.display = 'block';
}

// Shows the 'Next update in Xm' message in the flight synopsis bar
function displayNextUpdateCountdown() {
  let update_countdown = document.getElementById('update_countdown');

  if (!next_update_ts) {
    update_countdown.innerHTML = '';
    return;
  }

  // Number of seconds until the next update
  const remaining_time = (next_update_ts - (new Date())) / 1000;

  if (remaining_time >= 60) {
    update_countdown.innerHTML =
      `Update in <b>${Math.floor(remaining_time / 60)}m</b>`;
  } else if (remaining_time >= 0) {
    update_countdown.innerHTML =
      `Update in <b>&lt;1m</b>`;
  } else {
    // Can happen if the device went to sleep after last setTimeout()
    update_countdown.innerHTML = 'Update pending';
  }
}

// Displays progress by number of dots inside the button
function displayProgress(stage) {
  //  document.getElementById('go_button').textContent = '.'.repeat(stage);
  document.getElementById('go_button').textContent = '●'.repeat(stage);
}

// Cancels the next pending update, if any, set by setTimeout()
// in update()
function cancelPendingUpdate() {
  if (update_task) {
    clearTimeout(update_task);
    update_task = null;
  }
  next_update_ts = null;
  document.getElementById('update_countdown').innerHTML = '';
}

// Sets a timer to incrementally update the track at the end of
// next expected TX slot
function scheduleNextUpdate() {
  cancelPendingUpdate();

  const now = new Date();

  // Calculate when the next packet ends
  // WSPR packets start every 2 minutes (even minutes) and last 2 minutes
  // So the next packet end will be at the next even minute + 2 minutes
  const currentMinute = now.getUTCMinutes();
  const currentSecond = now.getUTCSeconds();

  // Find the next even minute start time
  let nextEvenMinute = currentMinute;
  if (currentMinute % 2 !== 0) {
    nextEvenMinute = currentMinute + 1; // Round up to next even minute
  } else if (currentSecond > 0) {
    nextEvenMinute = currentMinute + 2; // If we're past the start of current even minute, use next one
  }


  // Create the next update timestamp (packet end + 40 seconds)
  next_update_ts = new Date(now);

  // Handle minute rollover
  if (nextEvenMinute >= 60) {
    nextEvenMinute = nextEvenMinute % 60;
    next_update_ts.setUTCHours(next_update_ts.getUTCHours() + 1);
  }

  next_update_ts.setUTCMinutes(nextEvenMinute);
  next_update_ts.setUTCSeconds(40); // 40 seconds after packet ends
  next_update_ts.setUTCMilliseconds(0);

  // If the calculated time is in the past or too soon (less than 10 seconds away), 
  // schedule for the next packet cycle
  if (next_update_ts <= now || (next_update_ts - now) < 10000) {
    next_update_ts.setUTCMinutes((nextEvenMinute + 2) % 60);
  }

  // Add small randomization (0-5 seconds) to avoid hitting servers simultaneously
  const randomDelay = Math.floor(Math.random() * 5000);
  next_update_ts = new Date(next_update_ts.getTime() + randomDelay);

  if (debug > 0) {
    console.log('Next update: ', next_update_ts, `(in ${(next_update_ts - now) / 1000}s)`)
  }

  displayNextUpdateCountdown();

  update_task = setTimeout(() => {
    update(true);  // update incrementally
  }, next_update_ts - now);
}

// Fetch new data from wspr.live and update the map
async function update(incremental_update = false) {
  cancelPendingUpdate();

  const go_button = document.getElementById('go_button');

  try {
    // Disable the button and show progress
    go_button.disabled = true;

    let new_data = [];

    let stage = 1;
    displayProgress(stage++);

    const query = createWSPRLiveQuery(
      false /* fetch_q01 */,
      {
        'zachtek2': [0, 1], 'generic2': [0, 1],
        'unknown': [0, 1, 2, 3, 4]
      }[params.tracker] || [0]  /* slots */,
      incremental_update);
    new_data = importWSPRLiveData(await runQuery(query));

    displayProgress(stage++);

    if (params.tracker == 'u4b' || params.tracker == 'wb8elk') {
      // Fetch Q/0/1 callsign telemetry
      const slots = params.fetch_et ?
        Array.from({ length: params.fetch_et + 1 }, (_, i) => i + 1) :
        [1];
      const q01_query = createWSPRLiveQuery(
        true /* fetch_q01 */, slots, incremental_update);
      new_data.push(...importWSPRLiveData(await runQuery(q01_query)));
      displayProgress(stage++);
    }

    // Sort new_data by (ts, cs)
    new_data.sort((row1, row2) =>
      (row1.ts - row2.ts) ||
      (row1.cs > row2.cs) - (row1.cs < row2.cs));

    if (debug > 2) console.log(new_data);

    if (!incremental_update) {
      data = new_data;
    } else {
      const merge_result = mergeData(data, new_data);
      data = merge_result.data;

      // Show notification if new packets were received
      if (merge_result.new_count > 0) {
        // Check if notifications are enabled via checkbox
        const notificationsCheckbox = document.getElementById('notifications_enabled');
        if (notificationsCheckbox && notificationsCheckbox.checked) {
          // Request notification permission if not already done
          if (!notification_permission_requested) {
            notification_permission_requested = true;
            await requestNotificationPermission();
          }

          // Show notification
          const callsign = params.cs || 'tracker';
          showNewPacketNotification(merge_result.new_count, callsign);
        }
      }

      if (debug > 3) console.log(data);
    }

    spots = matchTelemetry(data);
    if (debug > 2) console.log(spots);

    decodeSpots();

    // Always display track since both map and data are visible
    displayTrack();

    // Recenter the map on first load
    if (!incremental_update && last_marker) {
      map.setView(last_marker.getLatLng(), map.getZoom(), { animate: false });
    }

    const now = new Date();
    last_update_ts = now;

    // Schedule automatic updates only for current flights (within 24 hours)
    if (now - params.end_date < 86400 * 1000) {
      scheduleNextUpdate();
    }
  } catch (error) {
    clearTrack();
    cancelPendingUpdate();
    if (error instanceof TypeError) {
      alert('WSPR Live request failed. ' +
        'Refresh the page to resume updates.');
    } else {
      alert(debug > 0 ? `\n${error.stack}` : error);
    }
  } finally {
    // Restore the submit button
    go_button.disabled = false;
    go_button.textContent = 'Go';
  }
}

// Updates the URL based on current params, for bookmarking etc
function updateURL() {
  try {
    let url = '';
    const presetSelect = document.getElementById('preset');
    const selectedPreset = presetSelect.value;

    if (selectedPreset && selectedPreset !== '') {
      // Using a preset - only include preset parameter
      // All configuration (including end_date) is handled by the preset
      url = '?preset=' + encodeURIComponent(selectedPreset);
    }

    // Only add additional parameters that are not controlled by presets
    if (units_param) {
      url += (url ? '&' : '?') + 'units=' + encodeURIComponent(units_param);
    }

    history.replaceState(null, '', url);
  } catch (error) {
    console.log('Security error triggered by history.replaceState()');
  }
}

// Similar to encodeURIComponent but does not escape ',' and ':', and
// escapes ' ' as '+'
function encodeURLParam(param) {
  return Array.from(param.replace(/\s/g, '+')).map(c =>
    ',:'.includes(c) ? c : encodeURIComponent(c)
  ).join('');
}

// Invoked when the "Go" button is pressed or when URL params are provided
// on load
function processSubmission(e, on_load = false) {
  last_data_view_scroll_pos = 0;
  cancelPendingUpdate();
  params = parseParams();
  if (params) {
    if (debug > 0) console.log(params);
    if (!on_load) {
      updateURL();
    }
    update();
  } else {
    clearTrack();
  }
}

// Table / charts

const kDataFields = [
  ['ts', {
    'label': 'Time UTC',
    'color': '#7b5d45',
    'type': 'timestamp'
  }],
  ['grid', { 
    'align': 'left',
    'formatter': (v, au) => v || '(No Location)'
  }],
  ['lat', {
    'label': 'Lat',
    'color': '#0066cc',
    'type': 'angle',
    'formatter': (v, au) => {
      if (v === undefined || v === null) return '(No Location)';
      try {
        return `${v.toFixed(6)}` + (au ? '°' : '');
      } catch (e) {
        return '(Invalid)';
      }
    }
  }],
  ['lon', {
    'label': 'Lon',
    'color': '#0066cc',
    'type': 'angle',
    'formatter': (v, au) => {
      if (v === undefined || v === null) return '(No Location)';
      try {
        return `${v.toFixed(6)}` + (au ? '°' : '');
      } catch (e) {
        return '(Invalid)';
      }
    }
  }],
  ['altitude', { 
    'graph': {},
    'formatter': (v, au) => {
      if (v === undefined || v === null) return '(No Location)';
      return formatAltitude(v, au);
    }
  }],
  ['vspeed', {
    'min_detail': 1,
    'label': 'VSpeed',
    'long_label': 'Vertical Speed',
    'graph': {}
  }],
  ['speed', { 'graph': {} }],
  ['cspeed', {
    'min_detail': 1,
    'type': 'speed',
    'label': 'CSpeed',
    'long_label': 'Computed Speed',
    'graph': {}
  }],
  ['voltage', { 'graph': {} }],
  ['temp', {
    'long_label': 'Temperature',
    'graph': {}
  }],
  ['power', {
    'min_detail': 1,
    'label': 'Pwr',
    'long_label': 'TX Power',
    'type': 'power',
    'graph': {},
  }],
  ['sun_elev', {
    'min_detail': 1,
    'label': 'Sun',
    'long_label': 'Sun Elevation',
    'type': 'angle',
    'graph': {},
  }],
  ['num_rx', {
    'min_detail': 1,
    'label': '# RX',
    'long_label': '# RX Reports',
    'graph': {},
  }],
  ['max_rx_dist', {
    'min_detail': 1,
    'type': 'distance',
    'label': 'Max RX',
    'long_label': 'Max RX distance',
    'graph': {}
  }],
  ['max_snr', {
    'min_detail': 1,
    'label': 'Max SNR',
    'graph': {},
    'type': 'snr'
  }]
];

const kDerivedFields = [
  'power', 'sun_elev', 'cspeed', 'vspeed', 'sun_elev', 'num_rx',
  'max_rx_dist', 'max_snr'];

const kFormatters = {
  'timestamp': (v, au) => formatTimestamp(v),
  'distance': formatDistance,
  'altitude': formatAltitude,
  'speed': formatSpeed,
  'vspeed': formatVSpeed,
  'voltage': formatVoltage,
  'temp': formatTemperature,
  'power': (v, au) => v + (au ? ' dBm' : ''),
  'snr': (v, au) => v + (au ? ' dB' : ''),
  'angle': (v, au) => v + (au ? '°' : '')
};

const kFetchers = {
  'distance': getDistanceInCurrentUnits,
  'altitude': getAltitudeInCurrentUnits,
  'speed': getSpeedInCurrentUnits,
  'vspeed': getVSpeedInCurrentUnits,
  'temp': getTemperatureInCurrentUnits
};

function computeDerivedData(spots) {
  let derived_data = {};
  for (const field of kDerivedFields) {
    derived_data[field] = new Array(spots.length).fill(undefined);
  }
  let last_altitude_spot = null;
  let last_good_spot = null;
  for (let i = 0; i < spots.length; i++) {
    const spot = spots[i];
    if (['u4b', 'generic1', 'generic2', 'unknown'].includes(params.tracker)) {
      // Handle orphaned spots that don't have slot 0
      if (spot.slots && spot.slots[0]) {
        derived_data['power'][i] = spot.slots[0]['power'];
      } else {
        derived_data['power'][i] = undefined;
      }
    }
    if (i > 0) {
      if (last_altitude_spot && spot.altitude) {
        // Calculate vspeed
        derived_data['vspeed'][i] =
          (spot.altitude - last_altitude_spot.altitude) * 60000 /
          ((spot.ts - last_altitude_spot.ts) || 1);
      }
      let currentSats = spot.et && spot.et[3] !== undefined ? spot.et[3] : null;
      if (params.tracker != 'unknown' && spot.grid && spot.grid.length >= 6 && currentSats !== 0 && 
          spot.lat !== undefined && spot.lat !== null && 
          spot.lon !== undefined && spot.lon !== null) {
        if (last_good_spot) {
          // If previous window only had 6-figure grid, only use 6-figure grid for current spot
          let currentGrid = spot.grid;
          let previousGrid = last_good_spot.grid;

          // If previous was 6-char and current is 8-char, truncate current to 6-char for calculation
          if (previousGrid.length === 6 && currentGrid.length === 8) {
            currentGrid = currentGrid.substring(0, 6);
            // Recalculate lat/lon using 6-char grid for speed calculation
            let [lat6, lon6] = maidenheadToLatLon(currentGrid);
            var currentLat = lat6;
            var currentLon = lon6;
          } else {
            var currentLat = spot.lat;
            var currentLon = spot.lon;
          }

          if (previousGrid.length === 8 && currentGrid.length === 6) {
            // If previous was 8-char and current is 6-char, truncate previous to 6-char for calculation
            previousGrid = previousGrid.substring(0, 6);
            // Recalculate lat/lon using 6-char grid for speed calculation
            let [lat6, lon6] = maidenheadToLatLon(previousGrid);
            var previousLat = lat6;
            var previousLon = lon6;
          } else {
            var previousLat = last_good_spot.lat;
            var previousLon = last_good_spot.lon;
          }

          // Calculate cspeed (computed speed) using lat/lon from grid squares
          let dist = L.latLng(previousLat, previousLon)
            .distanceTo([currentLat, currentLon]) / 1000;
          let ts_delta = (spot.ts - last_good_spot.ts) || 1;

          // Convert to km/h: distance(km) * 3600(s/h) / time(s)
          let cspeed = dist * 3600 / (ts_delta / 1000);

          // Use uncertainty based on the precision level actually used for calculation
          let effectiveGridLength = Math.min(previousGrid.length, currentGrid.length);
          let uncertainty_km = effectiveGridLength >= 8 ? 0.2 : 4; // 200m vs 4km
          let min_cspeed = Math.max(dist - uncertainty_km, 0) * 3600 / (ts_delta / 1000);
          let max_cspeed = (dist + uncertainty_km) * 3600 / (ts_delta / 1000);

          // More lenient acceptance criteria for 8-character grids due to higher precision
          let max_uncertainty = effectiveGridLength >= 8 ? 20 : 50; // km/h

          if (cspeed <= 350 &&
            (max_cspeed - min_cspeed <= max_uncertainty ||
              (cspeed >= 0 && cspeed <= 300))) {
            derived_data['cspeed'][i] = cspeed;
            last_good_spot = spot;
          }
        } else {
          last_good_spot = spot;
        }
      }
    }
    if (spot.altitude) last_altitude_spot = spot;
    
    // Handle orphaned spots that may not have lat/lon
    if (spot.lat !== undefined && spot.lat !== null && 
        spot.lon !== undefined && spot.lon !== null) {
      derived_data['sun_elev'][i] = getSunElevation(spot.ts, spot.lat, spot.lon);
    } else {
      derived_data['sun_elev'][i] = undefined;
    }
    
    [derived_data['num_rx'][i], derived_data['max_rx_dist'][i],
    derived_data['max_snr'][i]] = getRXStats(spot);
  }
  for (const field of kDerivedFields) {
    if (derived_data[field].every(v => v == undefined)) {
      delete derived_data[field];
    }
  }
  // Only keep power if some values are different
  if (derived_data['power'] &&
    new Set(derived_data['power'].filter(v => v != undefined)).size < 2) {
    delete derived_data['power'];
  }
  return derived_data;
}

function extractExtendedTelemetryData(spots) {
  let et_data = [];
  for (let i = 0; i < spots.length; i++) {
    const spot = spots[i];
    if (spot.raw_et) {
      spot.raw_et.forEach((v, slot) => {
        let field = `raw_et${slot}`;
        let field_data = et_data[field];
        if (!field_data) {
          field_data = new Array(spots.length).fill(undefined);
          et_data[field] = field_data;
        }
        field_data[i] = v;
      });
    }
    if (spot.et) {
      spot.et.forEach((v, slot) => {
        let field = `et${slot}`;
        let field_data = et_data[field];
        if (!field_data) {
          field_data = new Array(spots.length).fill(undefined);
          et_data[field] = field_data;
        }
        field_data[i] = v;
      });
    }
  }
  return et_data;
}

function createTableCell(type, content, align = null, color = null) {
  const cell = document.createElement(type);
  cell.textContent = content;
  if (align) {
    cell.style.textAlign = align;
  }
  if (color) {
    cell.style.color = color;
  }
  return cell;
}

function createPrettyButton(text, action) {
  const button = document.createElement('button');
  button.classList.add('pretty_button');
  button.textContent = text;
  button.addEventListener('click', action);
  return button;
}

function clearDataView() {
  let data_view = document.getElementById('data_view');
  if (data_view.u_plots) {
    for (let u_plot of data_view.u_plots) {
      u_plot.destroy();
    }
    delete data_view.u_plots;
  }
  data_view.innerHTML = '';
}

function getExtendedTelemetryAttributes(i) {
  let label = `ET${i}`;
  if (params.et_spec['labels'] && params.et_spec['labels'][i]) {
    label = params.et_spec['labels'][i];
  }
  let long_label = label;
  if (params.et_spec['long_labels'] && params.et_spec['long_labels'][i]) {
    long_label = params.et_spec['long_labels'][i];
  }
  let units;
  if (params.et_spec['units'] && params.et_spec['units'][i]) {
    units = params.et_spec['units'][i];
  }
  let resolution;
  if (params.et_spec['resolutions'] && params.et_spec['resolutions']) {
    resolution = params.et_spec['resolutions'][i];
  }
  let formatter = (v, au) => {
    if (resolution != null) v = v.toFixed(resolution);
    if (units && au) v += units;
    return v;
  };
  return [label, long_label, units, formatter];
}

// Create virtual spots for orphaned telemetry data (telemetry without location)
// Creates orphaned telemetry spots for U4B tracker when telemetry data
// is received but no corresponding Type 1 (location) message is available
function createOrphanedTelemetrySpots() {
  try {
    // Check if the feature is enabled
    const showOrphanedCheckbox = document.getElementById('show_orphaned_telemetry');
    if (!showOrphanedCheckbox || !showOrphanedCheckbox.checked) {
      return [];
    }
    
    if (params.tracker !== 'u4b' || !data || data.length === 0) {
      return [];
    }

    let orphaned_spots = [];
    let starting_minute = getU4BSlotMinute(0);
    
    // Find all data rows that were used in existing spots
    let used_rows = new Set();
    spots.forEach(spot => {
      if (spot.slots) {
        spot.slots.forEach(slot => {
          if (slot) used_rows.add(slot);
        });
      }
    });

    // Look for orphaned telemetry data
    data.forEach(row => {
      try {
        if (!used_rows.has(row)) {
          const slot = (((row.ts.getMinutes() - starting_minute) + 10) % 10) / 2;
          if (slot >= 1 && slot <= 4) { // Valid slot range
            // This is orphaned telemetry data, create a virtual spot
            let orphaned_spot = { 
              'slots': new Array(5), 
              'is_orphaned': true,
              'ts': row.ts,
              'grid': null,
              'lat': null,
              'lon': null,
              'altitude': null,
            };
            orphaned_spot.slots[slot] = row;
            
            // Process basic telemetry (slot 1)
            if (slot === 1 && row.cs && row.cs.length === 6) {
              try {
                const [m, n] = extractU4BQ01Payload(row);
                if (n % 2) { // Valid telemetry message
                  if (Math.floor(n / 2) % 2) { // Valid GPS bit
                    orphaned_spot.speed = (Math.floor(n / 4) % 42) * 2 * 1.852;
                    let voltage = ((Math.floor(n / 168) + 20) % 40) * 0.05 + 3;
                    if (params.scaleVoltage) {
                      voltage -= 2;
                    }
                    orphaned_spot.voltage = voltage;
                    orphaned_spot.temp = (Math.floor(n / 6720) % 90) - 50;
                    orphaned_spot.altitude = (m % 1068) * 20;
                  }
                }
              } catch (e) {
                if (debug > 0) console.error('Error processing basic telemetry:', e);
              }
            }
            
            // Process extended telemetry (slot 2+)
            if (slot >= 2 && row.cs && row.cs.length === 6) {
              try {
                const [m, n] = extractU4BQ01Payload(row);
                if (!(n % 2)) { // Extended telemetry message
                  const v = Math.floor((m * 615600 + n) / 2);
                  if (!orphaned_spot.raw_et) {
                    orphaned_spot.raw_et = [];
                  }
                  orphaned_spot.raw_et[slot] = v;
                }
              } catch (e) {
                if (debug > 0) console.error('Error processing extended telemetry:', e);
              }
            }
            
            orphaned_spots.push(orphaned_spot);
          }
        }
      } catch (e) {
        if (debug > 0) console.error('Error processing data row:', e);
      }
    });

    // Process extended telemetry for orphaned spots
    orphaned_spots.forEach(spot => {
      try {
        if (spot.raw_et && params.et_spec) {
          decodeExtendedTelemetry(spot);
        }
      } catch (e) {
        if (debug > 0) console.error('Error decoding extended telemetry:', e);
      }
    });

    return orphaned_spots;
  } catch (e) {
    if (debug > 0) console.error('Error in createOrphanedTelemetrySpots:', e);
    return [];
  }
}

function showDataView() {
  clearDataView();

  let data_view = document.getElementById('data_view');
  data_view.style.display = 'block';

  let div = document.createElement('div');
  div.id = 'data_view_wrapper';
  div.style.padding = '20px';

  let notice = document.createElement('div');
  if (is_mobile) {
    notice.innerHTML = 'Charts are touch-enabled, supporting pan and zoom gestures.';
  } else {
    notice.innerHTML = 'To <b>zoom in</b> on charts, click and drag. To <b>zoom out</b>, double click.';
  }
  notice.classList.add('notice');
  notice.style.marginBottom = '20px';
  div.appendChild(notice);

  // Create combined spots array including orphaned telemetry
  let orphaned_spots = createOrphanedTelemetrySpots();
  let combined_spots = orphaned_spots.length > 0 ? [...spots, ...orphaned_spots] : spots;
  
  // Sort by timestamp if we have orphaned spots
  if (orphaned_spots.length > 0) {
    combined_spots.sort((a, b) => a.ts - b.ts);
  }

  let supplementary_data =
  {
    ...computeDerivedData(combined_spots),
    ...extractExtendedTelemetryData(combined_spots)
  };

  // Find the union of all present fields
  const present_spot_fields = Object.fromEntries(
    [...new Set(combined_spots.flatMap(Object.keys))].map(f => [f, 1]));
  const present_supplementary_fields = Object.fromEntries(
    Object.keys(supplementary_data).map(f => [f, 1]));
  let present_fields = Object.fromEntries(
    [...Object.entries(present_spot_fields),
    ...Object.entries(present_supplementary_fields)]);

  // Prefill the table with row numbers
  let table_headers = ['#'];
  let long_headers = ['#'];
  let table_data = [Array.from(
    { length: combined_spots.length }, (_, i) => i + 1)];
  let field_specs = [{}];
  let table_formatters = [null];
  let table_fetchers = [null];

  let graph_labels = [];
  let graph_data_indices = [];  // indices into table_data
  const ts_values = combined_spots.map(spot => spot.ts.getTime() / 1000);

  // Add ET to the list of possible fields
  let data_fields = [...kDataFields];
  for (let i = 1; i < 5; i++) {
    if (supplementary_data[`raw_et${i}`]) {
      data_fields.push(
        [`raw_et${i}`,
        { 'color': '#7b5d45', 'label': `Raw ET${i}` }]);
    }
  }
  for (let i = 0; i < 32; i++) {
    if (supplementary_data[`et${i}`]) {
      const [label, long_label, units, formatter] =
        getExtendedTelemetryAttributes(i);

      // Don't show a graph for the "Loc" field
      const shouldShowGraph = label !== 'Loc';

      data_fields.push([`et${i}`,
      {
        'label': label, 'long_label': long_label, 'units': units,
        'formatter': formatter,
        ...(shouldShowGraph ? { 'graph': {} } : {})
      }]);
    }
  }

  // Iterate through possible fields
  for (const [field, spec] of data_fields) {
    if (!present_fields[field]) continue;
    // Always show all available fields - removed detail level filtering

    // Attach the correct formatter / fetcher
    let formatter = null;
    let fetcher = null;
    let type = spec.type || field;
    if (spec.formatter) {
      formatter = spec.formatter;
    } else {
      if (kFormatters[type]) {
        formatter = kFormatters[type];
      }
    }
    if (spec.fetcher) {
      fetcher = spec.fetcher;
    } else {
      if (kFetchers[type]) {
        fetcher = kFetchers[type];
      }
    }
    table_formatters.push(formatter);
    table_fetchers.push(fetcher);

    // Add table / graph labels
    const default_label = field[0].toUpperCase() + field.slice(1);
    let table_header = spec['label'] || default_label;
    let long_label =
      spec['long_label'] || spec['label'] || default_label;
    let units = spec['units'] ||
      (kUnitInfo[type] && kUnitInfo[type][params.units][0]);
    if (units) {
      long_label += ' (' + units.trim() + ')';
      table_header += '\n(' + units.trim() + ')';
    }
    table_headers.push(table_header);
    long_headers.push(long_label);
    field_specs.push(spec);
    if (spec.graph) {
      graph_labels.push(long_label);
      graph_data_indices.push(table_data.length);
    }

    // Data for this field
    let field_data;
    if (supplementary_data[field]) {
      field_data = supplementary_data[field];
    } else {
      field_data = combined_spots.map(spot =>
        spot[field] == undefined ?
          undefined : (spec.fetcher ?
            spec.fetcher(spot[field]) : spot[field]));
    }
    table_data.push(field_data);
  }

  // Add graphs
  data_view.u_plots = [];  // references to created uPlot instances
  for (let i = 0; i < graph_data_indices.length; i++) {
    let index = graph_data_indices[i];
    const opts = {
      tzDate: ts => uPlot.tzDate(new Date(ts * 1e3), 'Etc/UTC'),
      cursor: {
        drag: { x: true, y: true, uni: 20 },
        sync: { key: 1, setSeries: true, scales: ['x'] }
      },
      width: 600,
      height: 300,
      plugins: [touchZoomPlugin()],
      series: [{ label: 'Time UTC' },
      {
        label: graph_labels[i],
        stroke: 'blue',
        value: (self, value) => value
      }
      ],
      scales: [{ label: 'x' }],
      axes: [{}, { size: 52 }]
    };

    const fetcher = table_fetchers[index] || ((v) => v);
    data_view.u_plots.push(
      new uPlot(opts, [ts_values, table_data[index].map(
        (v) => (v == undefined) ? v : fetcher(v))], div));
  }

  div.appendChild(document.createElement('br'));

  div.appendChild(
    createPrettyButton('Toggle Units', toggleUnits));
  div.appendChild(
    createPrettyButton('Export CSV',
      () => downloadCSV(long_headers, table_data, table_formatters)));
  div.appendChild(
    createPrettyButton('Get Raw Data', () => downloadJSON(combined_spots)));

  // Populate the table
  let table = document.createElement('table');
  table.classList.add('data_table');
  // Fill the header
  let row = document.createElement('tr');
  for (let i = 0; i < table_headers.length; i++) {
    let th = createTableCell('th', table_headers[i]);
    th.title = long_headers[i];
    row.appendChild(th);
  }
  table.appendChild(row);

  for (let i = table_data[0].length - 1; i >= 0; i--) {
    let row = document.createElement('tr');
    for (let j = 0; j < table_data.length; j++) {
      let value = table_data[j][i];
      if (value == null) {
        value = '';
      } else {
        if (table_formatters[j]) {
          value = table_formatters[j](value, false /* append units */);
        }
      }
      const spec = field_specs[j];
      row.appendChild(createTableCell('td', value, spec.align, spec.color));
    }
    table.appendChild(row);
  }
  div.appendChild(table);
  data_view.appendChild(div);

  data_view.onscrollend = () => {
    last_data_view_scroll_pos = data_view.scrollTop;
  }

  setTimeout(() => {
    data_view.scrollTop = last_data_view_scroll_pos;
  }, 5);
}

function toggleDataViewDetail() {
  params.detail ^= 1;
  showDataView();

  // Remember user preference
  localStorage.setItem('detail', params.detail);
}

function getDownloadFilename(ext) {
  const raw_ch = document.getElementById('ch').value.trim().toUpperCase();
  return params.cs.toUpperCase().replace(/\//g, '_') + '_' + raw_ch + '_' +
    formatTimestamp(params.start_date).slice(0, 10).replace(/-/g, '') + '-' +
    formatTimestamp(params.end_date).slice(0, 10).replace(/-/g, '') +
    '.' + ext;
}

function downloadJSON(spots) {
  const json = JSON.stringify(spots,
    (key, value) => (value == undefined ? null : value));
  downloadFile(json, 'application/json', getDownloadFilename('json'));
}

function downloadCSV(headers, data, formatters) {
  let rows = [headers];
  for (let i = data[0].length - 1; i >= 0; i--) {
    let row = [];
    for (let j = 0; j < data.length; j++) {
      let value = data[j][i];
      if (value == null) {
        value = '';
      } else {
        if (formatters[j]) {
          value = formatters[j](value, false /* append_units */);
        }
      }
      row.push(value);
    }
    rows.push(row);
  }
  let csv = rows.map(row =>
    row.map(v => {
      v = String(v).replace(/"/g, '""');
      return /[",\r\n]/.test(v) ? `"${v}"` : v;
    }).join(',')
  ).join('\n');
  downloadFile(csv, 'text/csv', getDownloadFilename('csv'))
}

function downloadFile(data, mime_type, filename) {
  const blob = new Blob([data], { type: mime_type });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}

function closeDataView() {
  // Hide data view UI
  clearDataView();
  let data_view = document.getElementById('data_view');
  data_view.style.display = 'none';
}

// Prefills form fields from URL decorators
function initializeFormFields() {
  document.getElementById('cs').value = getUrlParameter('cs');
  document.getElementById('ch').value = getUrlParameter('ch');
  let band_param = getUrlParameter('band');
  if (!band_param || !(band_param in kWSPRBandInfo)) {
    band_param = '20m';
  }
  document.getElementById('band').value = band_param;
  let start_date_param = getUrlParameter('start_date');
  if (!start_date_param) {
    // Prefill to a date 1 month in the past
    start_date_param = formatTimestamp(
      new Date(new Date().setUTCMonth(new Date().getUTCMonth() - 1)))
      .slice(0, 10);
  }
  document.getElementById('start_date').value = start_date_param;
}

function parseExtendedTelemetrySpec() {
  if (!et_dec_param) return null;
  if (!/^[0-9ets,:_~.-]+$/.test(et_dec_param)) return null;
  let decoders = [];
  let num_extractors = 0;
  for (const decoder_spec of et_dec_param.toLowerCase().split('~')) {
    let uses_et0 = false;
    let [filters_spec, extractors_spec] = decoder_spec.split('_');
    // Parse filters
    let filters = [];
    if (filters_spec) {
      for (const filter_spec of filters_spec.split(',')) {
        let filter = filter_spec.split(':');
        if (filter.length == 2 && ['et0', 's'].includes(filter[0])) {
          filter[1] = Number(filter[1]);
          if (!Number.isInteger(filter[1]) || filter[1] < 0) return null;
          if (filter[0] == 'et0') {
            filters.push([1, 4, 0]);
            filters.push([4, 16, filter[1]]);
            filters.push([64, 5, 's']);
            uses_et0 = true;
            continue;
          }
        } else if (filter.length == 4 && filter[0] == 't') {
          filter = [filter[0], Number(filter[1]), Number(filter[2]),
          Number(filter[3])];
          if (!filter.slice(1).every(v => Number.isInteger(v)) ||
            filter[1] <= 0 || filter[2] <= 1 || filter[3] < 0) {
            return null;
          }
        } else if (filter.length == 3) {
          filter = [Number(filter[0]), Number(filter[1]),
          filter[2] == 's' ? 's' : Number(filter[2])];
          if (!filter.every(v => Number.isInteger(v) || v == 's') ||
            filter[0] <= 0 || filter[1] <= 1 || filter[2] < 0) {
            return null;
          }
        } else {
          return null;
        }
        filters.push(filter);
      }
    }
    // Parse extractors
    let extractors = [];

    let next_divisor = uses_et0 ? 320 : 1;  // used for 3-term extractor spec
    for (const extractor_spec of extractors_spec.split(',')) {
      let extractor = extractor_spec.split(':').map(Number);
      if (extractor.length == 3) {
        extractor.unshift(next_divisor);
      }
      if (extractor.length != 4) return null;
      for (let i = 0; i < extractor.length; i++) {
        if ((i <= 1) && (!Number.isInteger(extractor[i]) ||
          extractor[i] < 1)) {
          return null;
        }
        if (Number.isNaN(extractor[2])) return null;
        if (Number.isNaN(extractor[3]) || extractor[3] <= 0) return null;
        next_divisor = extractor[0] * extractor[1];
      }
      extractors.push(extractor);
    }
    decoders.push([filters, extractors]);
    num_extractors += extractors.length;
  }
  if (!decoders) return null;
  // Parse optional params
  let labels;
  let long_labels;
  let units;
  let resolutions;
  if (et_labels_param) {
    if (!/^[0-9a-z ,#_]+$/i.test(et_labels_param)) return null;
    labels = et_labels_param.split(',');
    if (!labels.every(v => v.length < 32)) return null;
  }
  if (et_llabels_param) {
    if (!/^[0-9a-z ,#_]+$/i.test(et_llabels_param)) return null;
    long_labels = et_llabels_param.split(',');
    if (!long_labels.every(v => v.length < 64)) return null;
  }
  if (et_units_param) {
    if (!/^[a-z /,]+$/i.test(et_units_param)) return null;
    units = et_units_param.split(',');
    if (!units.every(v => v.length < 8)) return null;
  }
  if (et_res_param) {
    resolutions = et_res_param.split(',').map(
      v => v == '' ? null : Number(v));
    if (!resolutions.every(
      v => v == null || (Number.isInteger(v) && v > 0 && v < 4))) {
      return null;
    }
  }
  let spec = { 'decoders': decoders };
  if (labels) spec['labels'] = labels;
  if (long_labels) spec['long_labels'] = long_labels;
  if (units) spec['units'] = units;
  if (resolutions) spec['resolutions'] = resolutions;
  return spec;
}

// Entry point
function Run() {
  initializeFormFields();

  end_date_param = getUrlParameter('end_date');
  units_param = getUrlParameter('units');
  et_dec_param = getUrlParameter('et_dec') || 'et0:0_1101:0:1,100:0:1,101:0:10,41:0:1';
  et_labels_param = getUrlParameter('et_labels') || 'Pres,Loc,Uptime,NumSats';
  et_llabels_param = getUrlParameter('et_llabels') || 'Pressure,,,Number_Of_Satellites';
  et_units_param = getUrlParameter('et_units') || ' hPa,, min';
  et_res_param = getUrlParameter('et_res');

  // On mobile devices, allow for a larger click area
  let click_tolerance = 0;
  const agent_regexp = new RegExp(
    'Mobi|Android|iPhone|iPad|iPod|Opera Mini|IEMobile|WPDesktop|' +
    'BlackBerry|BB|PlayBook');
  if (agent_regexp.test(navigator.userAgent)) {
    click_tolerance = 15;
    is_mobile = true;
  }

  // Recall previously stored map location and zoom level
  let init_lat = localStorage.getItem('lat') || 40;
  let init_lon = localStorage.getItem('lon') || -100;
  let init_zoom_level = localStorage.getItem('zoom_level') || 2;

  // Make the map div visible (if not already)
  document.getElementById('map').style.display = 'block';

  // Initialize the map
  map = L.map('map',
    {
      renderer: L.canvas({ tolerance: click_tolerance }),
      minZoom: 2,
      maxBounds: [[-85, -180], [85, 180]],
      worldCopyJump: false
    });

  // Use local English-label tiles for lower levels
  L.tileLayer(
    'osm_tiles/{z}/{x}/{y}.png',
    {
      maxZoom: 6,
      attribution:
        '<a href="https://github.com/wsprtv/wsprtv.github.io">' +
        'WSPR TV</a> | &copy; <a href="https://www.openstreetmap.org' +
        '/copyright">OpenStreetMap</a> contributors'
    }).addTo(map);

  // Use OSM-hosted tiles for higher levels
  L.tileLayer(
    'https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png',
    {
      minZoom: 7, maxZoom: 12,
      attribution:
        '<a href="https://github.com/wsprtv/wsprtv.github.io">' +
        'WSPR TV</a> | &copy; <a href="https://www.openstreetmap.org' +
        '/copyright">OpenStreetMap</a> contributors'
    }).addTo(map);

  map.setView([init_lat, init_lon], init_zoom_level);

  // Add day / night visualization and the scale indicator
  let terminator = L.terminator(
    {
      opacity: 0, fillOpacity: 0.3, interactive: false,
      longitudeRange: 360
    }).addTo(map);
  L.control.scale().addTo(map);

  // Draw the antimeridian
  L.polyline([[90, 180], [-90, 180]],
    { color: 'gray', weight: 2, dashArray: '8,5', opacity: 0.4 })
    .addTo(map).bringToBack();
  L.polyline([[90, -180], [-90, -180]],
    { color: 'gray', weight: 2, dashArray: '8,5', opacity: 0.4 })
    .addTo(map).bringToBack();


  // Draw the equator
  L.polyline([[0, -180], [0, 180]],
    { color: 'gray', weight: 1, opacity: 0.2 })
    .addTo(map).bringToBack();

  // On pan / zoom, save map location and zoom level
  map.on('moveend', function () {
    const center = map.getCenter();
    localStorage.setItem('lat', center.lat);
    localStorage.setItem('lon', center.lng);
  });
  map.on('zoomend', function () {
    localStorage.setItem('zoom_level', map.getZoom());
  });

  // Display auxiliary info for clicks on the map outside of markers
  map.on('click', onMapClick);

  // Load and initialize presets
  loadPresets();

  // Handle clicks on the "Go" button
  document.getElementById('go_button').addEventListener(
    'click', processSubmission);

  // Note: Show/close data button event listeners removed as data is now 
  // displayed inline automatically

  // Update UI elements that change over time (e.g. "X min ago" messages)
  setInterval(() => {
    displayNextUpdateCountdown();

    // Update the "Last ago" timestamp
    let last_age = document.getElementById('last_age');
    if (last_age && last_marker) {
      last_age.innerHTML = formatDuration(new Date(), last_marker.spot.ts);
    }
  }, 20 * 1000);

  // Update the terminator (day / night overlay) periodically
  setInterval(() => {
    terminator.setTime(new Date());
  }, 120 * 1000);
}

// Global variable to store presets
let presets = [];

// Load presets from configuration file
async function loadPresets() {
  try {
    const response = await fetch('presets.json');
    presets = await response.json();
    populatePresetDropdown();
    setupPresetEventListeners();

    // Check URL parameters after presets are loaded
    checkUrlParametersForPreset();

    // Submit the form if parameters were provided in the URL
    if (document.getElementById('cs').value) {
      processSubmission(null, true /* on_load */);
    }
  } catch (error) {
    console.error('Error loading presets:', error);
    // Show error message - no presets available
    const presetSelect = document.getElementById('preset');
    const errorOption = document.createElement('option');
    errorOption.value = '';
    errorOption.textContent = 'Error loading presets';
    presetSelect.appendChild(errorOption);

    document.getElementById('config_info').innerHTML = 'Error: Could not load preset configuration';
  }
}

// Populate the preset dropdown
function populatePresetDropdown() {
  const presetSelect = document.getElementById('preset');

  // Clear existing options except the first one
  while (presetSelect.children.length > 1) {
    presetSelect.removeChild(presetSelect.lastChild);
  }

  // Add preset options
  presets.forEach((preset) => {
    const option = document.createElement('option');
    option.value = preset.name;
    option.textContent = preset.name;
    presetSelect.appendChild(option);
  });
}

// Setup event listeners for preset selection
function setupPresetEventListeners() {
  const presetSelect = document.getElementById('preset');
  const csInput = document.getElementById('cs');
  const chInput = document.getElementById('ch');
  const bandInput = document.getElementById('band');
  const startDateInput = document.getElementById('start_date');
  const endDateInput = document.getElementById('end_date');
  const configInfo = document.getElementById('config_info');
  const notificationsCheckbox = document.getElementById('notifications_enabled');

  // Notification checkbox event listener
  notificationsCheckbox.addEventListener('change', async function () {
    if (this.checked) {
      // Try to enable notifications
      const granted = await requestNotificationPermission();
      if (!granted) {
        // Permission denied, uncheck the box
        this.checked = false;
        alert('Notification permission was denied. Please enable notifications in your browser settings if you want to receive alerts.');
      }
    } else {
      // Disable notifications
      notifications_enabled = false;
    }

    // Save preference
    localStorage.setItem('notifications_enabled', this.checked.toString());
  });

  // Restore notification preference
  const savedNotificationPref = localStorage.getItem('notifications_enabled');
  if (savedNotificationPref === 'true') {
    notificationsCheckbox.checked = true;
    // Try to enable notifications silently (if permission already granted)
    if (Notification.permission === 'granted') {
      notifications_enabled = true;
    }
  }

  // Orphaned telemetry checkbox event listener
  const orphanedTelemetryCheckbox = document.getElementById('show_orphaned_telemetry');
  orphanedTelemetryCheckbox.addEventListener('change', function () {
    // Save preference
    localStorage.setItem('show_orphaned_telemetry', this.checked.toString());
    
    // Refresh the data view to show/hide orphaned telemetry
    if (spots && spots.length > 0) {
      showDataView();
    }
  });

  // Restore orphaned telemetry preference
  const savedOrphanedPref = localStorage.getItem('show_orphaned_telemetry');
  if (savedOrphanedPref !== null) {
    orphanedTelemetryCheckbox.checked = savedOrphanedPref === 'true';
  } // Default is checked (as set in HTML)

  // Grid filtering checkbox event listener
  const gridFilteringCheckbox = document.getElementById('enable_grid_filtering');
  gridFilteringCheckbox.addEventListener('change', function () {
    // Save preference
    localStorage.setItem('enable_grid_filtering', this.checked.toString());
    
    if (debug > 0) console.log('Grid filtering changed to:', this.checked);
    
    // Refresh the map to apply/remove grid filtering
    if (spots && spots.length > 0) {
      displayTrack();
    }
  });

  // Restore grid filtering preference
  const savedGridFilteringPref = localStorage.getItem('enable_grid_filtering');
  if (savedGridFilteringPref !== null) {
    gridFilteringCheckbox.checked = savedGridFilteringPref === 'true';
  } // Default is checked (as set in HTML)

  presetSelect.addEventListener('change', function () {
    if (this.value === '') {
      // "Select Preset..." option selected
      csInput.value = '';
      chInput.value = '';
      bandInput.value = '';
      startDateInput.value = '';
      endDateInput.value = '';
      configInfo.innerHTML = '';
      // Clear extended telemetry parameters
      et_dec_param = '';
      et_labels_param = '';
      et_llabels_param = '';
      et_units_param = '';
      et_res_param = '';
      scaleVoltage_param = false;
      return;
    }

    // Preset selected
    const presetName = this.value;
    const preset = presets.find(p => p.name === presetName);

    if (preset) {
      // Apply preset values
      csInput.value = preset.callsign || '';
      chInput.value = preset.channel || '';
      bandInput.value = preset.band || '20m';
      startDateInput.value = preset.start_date || '';
      endDateInput.value = preset.end_date || '';

      // Update info display
      const startDateText = preset.start_date || 'Auto';
      const endDateText = preset.end_date || 'Auto';
      configInfo.innerHTML = `Band: ${preset.band || '20m'}, Start: ${startDateText}, End: ${endDateText}`;

      // Set extended telemetry parameters
      et_dec_param = preset.et_dec || '';
      et_labels_param = preset.et_labels || '';
      et_llabels_param = preset.et_llabels || '';
      et_units_param = preset.et_units || '';
      et_res_param = preset.et_res || '';
      scaleVoltage_param = preset.scaleVoltage || false;
    }
  });
}

// Check if URL parameters should override preset selection
function checkUrlParametersForPreset() {
  const presetParam = getUrlParameter('preset');

  if (presetParam) {
    // Preset specified in URL
    const preset = presets.find(p => p.name === presetParam);
    if (preset) {
      document.getElementById('preset').value = presetParam;
      // Trigger the change event to apply the preset
      document.getElementById('preset').dispatchEvent(new Event('change'));
      return;
    }
  }

  // If no valid preset parameter found, default to first preset if available
  if (presets.length > 0) {
    document.getElementById('preset').value = presets[0].name;
    document.getElementById('preset').dispatchEvent(new Event('change'));
  }
}

Run();
