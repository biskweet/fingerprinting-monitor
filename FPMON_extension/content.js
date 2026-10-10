// Disclaimer: I asked Claude to optimize the extension as it originally caused an abnormally high CPU and RAM consumption (like, GB to high).
var s = document.createElement("script"),
    glob_extension_score = {},
    glob_csv = "",
    dl_flag = 0;
 
function inject() {
    // PATCH: tunables. Stack traces (per-script attribution, ~5 us each) are captured for the first
    // FPMON_FULL_CAPTURE_CALLS calls of each API, then for a random 1 in FPMON_SAMPLE_EVERY calls; every
    // call is still counted. A script that only touches an API after another script has called it more
    // than FPMON_FULL_CAPTURE_CALLS times can therefore go unattributed for that API.
    // Set FPMON_FULL_CAPTURE_CALLS = Infinity to attribute every call like the original (slow).
    var FPMON_FULL_CAPTURE_CALLS = 1000,
        FPMON_SAMPLE_EVERY = 100,
        FPMON_MAX_RECORDS_PER_SCRIPT = 500,     // cap on script_origins_calls[src].data
        FPMON_MAX_FP_SEQUENCE_PER_SCRIPT = 500, // cap on script_origins_internal[src].fingerprint
        FPMON_MAX_ACCUMULATED_CHARS = 20000;    // cap on strings accumulated for canPlayType/getItem/...
    var e = {},
        t = {},
        r = {},
        o = {},
        a = 0,
        n = 0,
        c = 0,
        s = {},
        p = {},
        g = 0,
        _ = 0,
        l = {},
        m = [
            ["VAR: property.subproperty", "NOarguments", "return value", "size of RV", "count"],
            ["FUN: function call", "arguments", "return value", "size of RV", "count"]
        ],
        u = [...m],
        f = "",
        d = new Set(); // PATCH: was an array re-deduplicated on every tick
    // PATCH: bookkeeping that replaces the unbounded per-call logs
    var fpmonSeen = new Set(u.map(function(e) {
            return e[0]
        })),
        fpmonCalls = Object.create(null),
        fpmonCategoryCache = new Map,
        fpmonCatCounts = {},
        fpmonUnsampled = 0,
        fpmonPVersion = 0,
        fpmonPostedPVersion = -1,
        fpmonSummary = null,
        fpmonRowIdx = new Map, // PATCH: entity name -> index in m (m used to be scanned on every call)
        fpmonBoolProps = ["geolocation", "WebGLRenderingContext", "localStorage", "sessionStorage", "openDatabase", "indexedDB", "addBehavior", "history", "DeprecatedStorageQuota"],
        fpmonOrig = Object.create(null),
        fpmonTZ, fpmonDevicesJSON, fpmonDevicesAt = -1e9,
        fpmonHandleSeparately = ["canPlayType()", "getItem()", "setItem()", "getParameter()", "getExtension()"],
        fpmonRandom = Math.random; // captured before page scripts can replace it
 
    // PATCH: b() only ever reads row[0], so one row per entity is enough (was one row per call, forever).
    // Consequence: fingerprint_categories_all now lists a category once per API instead of once per call;
    // the exact per-category call counts are in the new fingerprint_category_counts field.
    function fpmonTrackRow(e) {
        fpmonSeen.has(e[0]) || (fpmonSeen.add(e[0]), u.push(e))
    }
 
    // PATCH: same effect as the old "find the row by name, replace it (unless special) or push it" loops
    function fpmonPutRow(e, t) {
        var r = fpmonRowIdx.get(e[0]);
        void 0 === r ? (fpmonRowIdx.set(e[0], m.length), m.push(e)) : t && (m[r] = e)
    }
 
    // PATCH: refresh the call count of an existing row (lives here because w() has its own local m)
    function fpmonRefreshCount(e, t) {
        var r = fpmonRowIdx.get(e);
        return void 0 !== r && (-1 === fpmonHandleSeparately.indexOf(e) && (m[r][4] = t + ""), !0)
    }
 
    // PATCH: typed arrays (bufferData, readPixels, ...) are summarized instead of serialized element by element
    function fpmonArgReplacer(e, t) {
        return ArrayBuffer.isView(t) ? t.constructor.name + "(" + t.byteLength + "B)" : t
    }
 
    function fpmonStringifyArgs(e) {
        for (var t = 0; t < e.length; t++)
            if (ArrayBuffer.isView(e[t])) return JSON.stringify(e, fpmonArgReplacer);
        return JSON.stringify(e)
    }
 
    function fpmonAppendCapped(e, t) {
        return e = String(e), e.length >= FPMON_MAX_ACCUMULATED_CHARS ? e : (e = e + ";" + t, e.length < FPMON_MAX_ACCUMULATED_CHARS ? e : e.slice(0, FPMON_MAX_ACCUMULATED_CHARS) + ";[truncated]")
    }
 
    // PATCH: the per-call accumulation for canPlayType/getItem/setItem/getParameter/getExtension, now capped
    function fpmonAccumulate(e, t, r) {
        for (var o = 0; o < e.length; o++) {
            var a = fpmonRowIdx.get(e[o]);
            if (void 0 !== a) {
                if (String(m[a][1]).length < FPMON_MAX_ACCUMULATED_CHARS) {
                    var n = fpmonStringifyArgs(t);
                    m[a][1] = fpmonAppendCapped(m[a][1], "{}" === n ? "" : n)
                }
                m[a][2] = fpmonAppendCapped(m[a][2], r), m[a][4] = parseInt(m[a][4], 10) + 1 + ""
            }
        }
    }
 
    function fpmonCategory(e) {
        var t = fpmonCategoryCache.get(e);
        if (void 0 === t) {
            t = "unknown";
            for (var r in l)
                if (l[r].includes(e)) {
                    t = r;
                    break
                } fpmonCategoryCache.set(e, t)
        }
        return t
    }
 
    // PATCH: live value of a monitored property (was a snapshot taken at injection, keyed by name only)
    function fpmonOriginal(e, t) {
        var r = fpmonOrig[e + "." + t];
        return r ? r.get ? r.get.call(r.obj) : r.value : void 0
    }
 
    function fpmonTimeZone(e) {
        return void 0 === fpmonTZ && (fpmonTZ = e.DateTimeFormat().resolvedOptions().timeZone), fpmonTZ
    }
 
    // PATCH: was an enumerateDevices() on every read, and a TypeError on insecure origins
    function fpmonEnumerateDevices(e) {
        var t = Date.now();
        !e || "function" != typeof e.enumerateDevices || t - fpmonDevicesAt < 5e3 || (fpmonDevicesAt = t, e.enumerateDevices().then(function(e) {
            fpmonDevicesJSON = JSON.stringify(e.map(function(e) {
                return "id=" + e.deviceId + ";gid=" + e.groupId + ";" + e.kind + ";" + e.label
            }));
            for (var t = m.length - 1; t >= 0; t--) "navigator.mediaDevices" === m[t][0] && (m[t][2] = fpmonDevicesJSON)
        }, function() {}))
    }
 
    function v(e, t) {
        l[t] = e
    }
 
    function h(e, t, r, o, a, n) {
        for (var i = 0; i < t.length; i++)
            if (u[e][0] === t[i]) {
                for (var c = 0, s = 0; s < m.length; s++)
                    if (m[s][0] === t[i]) {
                        c = s;
                        break
                    } for (var p = 0, g = 0; g < m[c].length; g++) m[c][g] === r && (p = 1);
                0 === p && (m[c].push(r), d.add(r + ":" + o + ":" + a + ":" + n)), f += r + ";", fpmonCatCounts[r] = (fpmonCatCounts[r] || 0) + (fpmonCalls[u[e][0]] || 0)
            }
    }
 
    function b() {
        aggro = 1, naggro = 0;
        for (var e = 0; e < u.length; e++) h(e, fp_metric_canvas, "Canvas", aggro, .9, 1), h(e, fp_metric_jsfonts, "JS_fonts", aggro, .9, 1), h(e, fp_metric_list_of_plugins, "List_of_plugins", aggro, .9, 1), h(e, fp_metric_webgl, "WebGL", aggro, .9, 1), h(e, fp_metric_webdriver, "Webdriver", aggro, .25, 1), h(e, fp_metric_flash, "Flash", naggro, .4, 1), h(e, fp_metric_enabled_cookies, "Cookies_enabled", naggro, .25, 1), h(e, fp_metric_java_enabled, "Java_enabled", naggro, .4, 1), h(e, fp_metric_audio_video_formats, "Audio_Video_formats", aggro, .5, 1), h(e, fp_metric_audio, "Audio", aggro, .9, 1), h(e, fp_metric_media_devices, "Media_devices", aggro, .9, 1), h(e, fp_metric_frequency_analyzer, "Frequency_analyzer", aggro, .9, 1), h(e, fp_metric_geolocation, "Geolocation", aggro, .7, 1), h(e, fp_metric_connection, "Connection", aggro, .75, 1), h(e, fp_metric_timezone, "Timezone", naggro, .75, 1), h(e, fp_metric_content_language, "Content_language", naggro, .75, 1), h(e, fp_metric_browser_language, "Browser_language", naggro, .75, 1), h(e, fp_metric_system_language, "System_language", naggro, .75, 1), h(e, fp_metric_navigator_onLine, "Online", naggro, .1, 1), h(e, fp_metric_userAgent, "User_agent", naggro, .9, 1), h(e, fp_metric_appVersion, "App_version", aggro, .75, 1), h(e, fp_metric_buildID, "Build_ID", naggro, .2, 1), h(e, fp_metric_permissions, "Permissions", aggro, .5, 1), h(e, fp_metric_product, "Product", naggro, .4, 1), h(e, fp_metric_product_sub, "Product_sub", aggro, .4, 1), h(e, fp_metric_vendor, "Vendor", naggro, .4, 1), h(e, fp_metric_vendor_sub, "Vendor_sub", naggro, .4, 1), h(e, fp_metric_appCodeName, "App_code_name", naggro, .2, 1), h(e, fp_metric_appName, "App_name", naggro, .2, 1), h(e, fp_metric_storage, "Storage", naggro, .25, 1), h(e, fp_metric_dragDrop, "Drag_and_drop", naggro, .1, 1), h(e, fp_metric_donottrack, "DoNotTrack", naggro, .2, 1), h(e, fp_metric_platform, "Platform", naggro, .25, 1), h(e, fp_metric_oscpu, "Oscpu", aggro, .1, 1), h(e, fp_metric_battery, "Battery_status", aggro, .7, 1), h(e, fp_metric_device_memory, "Device_memory", aggro, .5, 1), h(e, fp_metric_cpuClass, "Cpu_Class", naggro, .5, 1), h(e, fp_metric_hardwareConcurrency, "Hardware_concurrency", aggro, .2, 1), h(e, fp_metric_mobile, "Mobile", naggro, .3, 1);
        return m
    }
    fp_metric_userAgent = ["navigator.userAgent"], fp_metric_platform = ["navigator.platform"], fp_metric_enabled_cookies = ["navigator.cookieEnabled"], fp_metric_timezone = ["getTimezoneOffset()", "window.Intl"], fp_metric_content_language = ["navigator.languages", "navigator.userLanguage", "navigator.language"], fp_metric_canvas = ["getImageData()", "getLineDash()", "measureText()", "isPointInPath()"], fp_metric_audio = ["createAnalyser()", "createOscillator()", "createGain()", "createScriptProcessor()", "createDynamicsCompressor()"], fp_metric_jsfonts = ["fill()", "fillText()"], fp_metric_donottrack = ["navigator.doNotTrack", "navigator.msDoNotTrack"], fp_metric_buildID = ["navigator.buildID"], fp_metric_product = ["navigator.product"], fp_metric_product_sub = ["navigator.productSub"], fp_metric_vendor = ["navigator.vendor"], fp_metric_vendor_sub = ["navigator.vendorSub"], fp_metric_hardwareConcurrency = ["navigator.hardwareConcurrency"], fp_metric_java_enabled = ["navigator.enabled"], fp_metric_device_memory = ["navigator.deviceMemory"], fp_metric_list_of_plugins = ["navigator.plugins"], fp_metric_permissions = ["navigator.permissions"], fp_metric_webgl = ["getParameter()", "getSupportedExtensions()", "getContextAttributes()", "getShaderPrecisionFormat()", "getExtension()", "readPixels()", "getUniformLocation()", "getAttribLocation()", "clearColor()", "enable()", "depthFunc()", "clear()", "createBuffer()", "bindBuffer()", "bufferData()", "createProgram()", "createShader()", "shaderSource()", "compileShader()", "attachShader()", "linkProgram()", "useProgram()", "drawArrays()"], fp_metric_storage = ["window.sessionStorage", "window.localStorage", "window.indexedDB", "window.openDatabase", "navigator.webkitTemporaryStorage", "navigator.webkitPersistentStorage", "navigator.openDatabase", "navigator.localStorage"], fp_metric_audio_video_formats = ["canPlayType()"], fp_metric_media_devices = ["navigator.mediaDevices"], fp_metric_frequency_analyzer = ["getFloatFrequencyData()", "getByteFrequencyData()", "getFloatTimeDomainData()", "getByteTimeDomainData()"], fp_metric_battery = ["navigator.getBattery"], fp_metric_oscpu = ["navigator.oscpu"], fp_metric_webdriver = ["window.webdriver", "navigator.webdriver"], fp_metric_cpuClass = ["navigator.cpuClass"], fp_metric_geolocation = ["navigator.geolocation"], fp_metric_appCodeName = ["navigator.appCodeName"], fp_metric_appName = ["navigator.appName"], fp_metric_appVersion = ["navigator.appVersion"], fp_metric_navigator_onLine = ["navigator.onLine"], fp_metric_browser_language = ["navigator.browserLanguage"], fp_metric_system_language = ["navigator.systemLanguage"], fp_metric_dragDrop = ["navigator.dragDrop"], fp_metric_flash = ["window.swfobject"], fp_metric_connection = ["navigator.connection"], fp_metric_mobile = ["window.ondeviceproximity", "window.onuserproximity", "window.DeviceOrientationEvent", "window.DeviceMotionEvent", "navigator.maxTouchPoints", "navigator.msMaxTouchPoints", "navigator.touch"], fp_metric_screen_window = ["window.devicePixelRatio", "window.innerWidth", "window.innerHeight", "window.emit", "window.outerWidth", "window.outerHeight", "screen.colorDepth", "screen.width", "screen.availWidth", "screen.availHeight", "screen.pixelDepth", "screen.height", "screen.availTop", "screen.availLeft", "screen.deviceXDPI", "screen.logicalXDPI", "screen.fontSmoothingEnabled", "screen.screenInfo", "navigator.orientation"], v(fp_metric_canvas, "Canvas"), v(fp_metric_jsfonts, "JS_fonts"), v(fp_metric_list_of_plugins, "List_of_plugins"), v(fp_metric_webgl, "WebGL"), v(fp_metric_webdriver, "Webdriver"), v(fp_metric_flash, "Flash"), v(fp_metric_enabled_cookies, "Cookies_enabled"), v(fp_metric_java_enabled, "Java_enabled"), v(fp_metric_audio_video_formats, "Audio_Video_formats"), v(fp_metric_audio, "Audio"), v(fp_metric_media_devices, "Media_devices"), v(fp_metric_frequency_analyzer, "Frequency_analyzer"), v(fp_metric_geolocation, "Geolocation"), v(fp_metric_connection, "Connection"), v(fp_metric_timezone, "Timezone"), v(fp_metric_content_language, "Content_language"), v(fp_metric_browser_language, "Browser_language"), v(fp_metric_system_language, "System_language"), v(fp_metric_navigator_onLine, "Online"), v(fp_metric_userAgent, "User_agent"), v(fp_metric_appVersion, "App_version"), v(fp_metric_buildID, "Build_ID"), v(fp_metric_permissions, "Permissions"), v(fp_metric_product, "Product"), v(fp_metric_product_sub, "Product_sub"), v(fp_metric_vendor, "Vendor"), v(fp_metric_vendor_sub, "Vendor_sub"), v(fp_metric_appCodeName, "App_code_name"), v(fp_metric_appName, "App_name"), v(fp_metric_storage, "Storage"), v(fp_metric_dragDrop, "Drag_and_drop"), v(fp_metric_donottrack, "DoNotTrack"), v(fp_metric_platform, "Platform"), v(fp_metric_oscpu, "Oscpu"), v(fp_metric_battery, "Battery_status"), v(fp_metric_device_memory, "Device_memory"), v(fp_metric_cpuClass, "Cpu_Class"), v(fp_metric_hardwareConcurrency, "Hardware_concurrency"), v(fp_metric_mobile, "Mobile"), v(fp_metric_screen_window, "Screen_window");
    var y = function(e, t) {
        var r = [];
        return null == e ? r : Array.prototype.map && e.map === Array.prototype.map ? e.map(t) : (function(e, t) {
            if (Array.prototype.forEach && e.forEach === Array.prototype.forEach) e.forEach(t);
            else if (e.length === +e.length)
                for (var r = 0, o = e.length; r < o; r++) t(e[r], r, e);
            else
                for (var a in e) e.hasOwnProperty(a) && t(e[a], a, e)
        }(e, function(e, o, a) {
            r.push(t(e, o, a))
        }), r)
    };
 
    function w(e, t, r, o, a) {
        // PATCH: every call is counted; the expensive stack capture only runs on sampled calls
        var fpmonN = fpmonCalls[e] = (fpmonCalls[e] || 0) + 1;
        if (fpmonN <= FPMON_FULL_CAPTURE_CALLS || fpmonRandom() * FPMON_SAMPLE_EVERY < 1) { // random: a fixed stride can alias with interleaved callers
            var n = function() {
                let e = Error.prepareStackTrace;
                var t = {};
                try {
                    var err, first, file, i; // PATCH: err and i were implicit globals (could hang page loops using an undeclared i)
                    for (Error.prepareStackTrace = function(e, t) {
                            return t
                        }, err = new Error, first = err.stack[0].getFileName(), i = 0; i < err.stack.length; i++)
                        if (file = err.stack[i].getFileName(), null != file && first !== file) {
                            t.file = file;
                            break
                        }
                } catch (e) {}
                return Error.prepareStackTrace = e, t
            }();
            var call_source = n.file; // PATCH: was an implicit global
            delete n.file, n.functioncall = e, n.category = fpmonCategory(e);
            try {
                a.toString().includes("Storage") ? localStorage === a ? n.object = "[object LocalStorage]" : sessionStorage === a ? n.object = "[object sessionStorage]" : n.object = a.toString() : n.object = a.toString()
            } catch (e) {
                n.object = "error: " + e
            }
            call_source in s || (s[call_source] = {
                idx: g,
                length: 0,
                data: []
            }, p[call_source] = {
                score: 0,
                unique_categories: [],
                fingerprint: []
            }, g++, fpmonPVersion++), n.idx = s[call_source].length, n.gidx = _, _++, "unknown" == n.category || p[call_source].unique_categories.includes(n.category) || (p[call_source].unique_categories.push(n.category), p[call_source].score = p[call_source].unique_categories.length), "unknown" != n.category && (p[call_source].fingerprint.length < FPMON_MAX_FP_SEQUENCE_PER_SCRIPT && p[call_source].fingerprint.push(n.category), p[call_source].fingerprint_calls = (p[call_source].fingerprint_calls || 0) + 1, fpmonPVersion++), s[call_source].data.length < FPMON_MAX_RECORDS_PER_SCRIPT && s[call_source].data.push(n), s[call_source].length++
        } else {
            fpmonUnsampled++;
            // PATCH: an unsampled call only refreshes the call count of its row in m; the row's arguments and
            // return value (never exported anywhere) keep the values of the last sampled call
            if (fpmonRefreshCount(e, o)) return null
        }
        var c, m = [];
        try {
            var fpmonArgs = fpmonStringifyArgs(t); // PATCH: stringified once (was up to 3 times)
            m.push(e), "{}" === fpmonArgs ? m.push("") : '""' === fpmonArgs ? m.push(t) : m.push(fpmonArgs);
            var u = "";
            u = "object" == typeof(c = r) ? null === c ? "null" : c : "function" == typeof c || c instanceof Function ? c.toString().slice(9).slice(0, -18) : c, "undefined" === r || void 0 === typeof r ? m.push("") : m.push(u + ""), m.push("0"), m.push(o + "")
        } catch (e) {}
        return m
    }
 
    function S(e, t) {
        f = "", fpmonCatCounts = {};
        n = c + 41 + 12 + 16;
        var r = b(),
            o = function(e) {
                for (var t = "", r = e.split(";"), o = 0; o < r.length; o++) {
                    let e = r[o];
                    t.includes(e) || (t += e + ";")
                }
                return t
            }(f),
            a = "";
        "" == o ? a = 0 : (";" == o.slice(-1) && (o = o.slice(0, -1)), a = o.split(";").length);
        var i = [...d],
            g = function(e) {
                for (var t = "", r = 2; r < e.length; r++) {
                    let o = e[r][0];
                    o.includes("()") && (o = o.split("(")[0] + "()"), t.includes(o) || (t += o + ";")
                }
                return t
            }(m),
            l = Math.ceil((r.length - 2) / n * 100) + "%",
            u = Math.ceil(a / 40 * 100) + "%",
            v = l + " (" + (r.length - 2) + "/" + n + ")",
            h = u + " (" + a + "/40)",
            y = window.location.href,
            w = function(e) {
                for (var t = 0, r = 0; r < e.length; r++) 1 == e[r].split(":")[1] && (t += 1);
                return t
            }(i),
            S = Math.ceil(w / 18 * 100) + "%",
            D = Math.ceil(w / a * 100) + "% (" + w + "/" + a + ")";
        1 == D.includes("NaN") && (D = "0% (" + w + "/" + a + ")");
        var N = S + " (" + w + "/18)",
            x = s,
            timestamp = (new Date).getTime(); // PATCH: was an implicit global (clobbered pages' own "timestamp")
        script_based_page_fps = [], Object.keys(p).sort().forEach(function(e, t) {
            script_calls_cnt = p[e].fingerprint.length, script_fp = p[e].fingerprint.join(";"), script_score = p[e].unique_categories.length, fixed_url = e, e.includes("?") && (fixed_url = e.split("?")[0]), fixed_url.includes(".js") && p[e].fingerprint.length && script_based_page_fps.push(script_fp)
        }), fpmonSummary = { // PATCH: the full JSON (with every call record) is now built on demand only
            url: y,
            date: timestamp,
            coverage_entities: v,
            coverage_categories: h,
            aggressive_coverage: N,
            aggressive_categories: D,
            fingerprint_categories: o,
            fingerprint_categories_all: f,
            loadtime: e,
            TIMEOUT: t,
            score: a,
            entities_all: g
        }, glob_csv = [y, v, h, N, D, a, e, t, timestamp, o, f, g, x].join(", ")
    }
 
    // PATCH: same JSON as the old glob_extension_score (same key order); script_origins_calls only when full
    function fpmonScoreJSON(e) {
        if (!fpmonSummary) return;
        var t = {};
        for (var r in fpmonSummary) t[r] = fpmonSummary[r];
        return e && (t.script_origins_calls = s), t.script_origins_calls_cnt = _, t.script_origins_calls_unsampled = fpmonUnsampled, t.fingerprint_category_counts = fpmonCatCounts, JSON.stringify(t)
    }
 
    // PATCH: periodic updates carry the small summary; per-script data only when it changed
    function fpmonPublish() {
        D(fpmonScoreJSON(!1)), fpmonPVersion !== fpmonPostedPVersion && (fpmonPostedPVersion = fpmonPVersion, D(JSON.stringify(p), "script_origins_internal"))
    }
 
    function D(e, t = "glob_extension_score") {
        window.postMessage({
            type: t,
            text: e
        }, "*")
    }
    detectFingerprinting = function() {
        function n(e) {
            var t = e.obj[e.propName],
                a = e.obj,
                // PATCH: everything derived from t.toString() is computed once here (was ~8 times per call)
                tSrc = "function" == typeof t ? t.toString() : "",
                tSkip = tSrc.includes("function ()"),
                tName = tSrc.split(" ")[1],
                tSpecial = fpmonHandleSeparately.filter(function(e) {
                    return tSrc.includes(e)
                }),
                wrapper = function() {
                    if ("function" != typeof t) return;
                    let e = arguments;
                    var n = t.apply(this, e); // PATCH: exceptions propagate like the native method (were swallowed)
                    var i = n;
                    if (void 0 === i && (i = "undefined"), null === i && (i = "null"), tSkip) return n;
                    tSpecial.length && fpmonAccumulate(tSpecial, e, i);
                    var is = i.toString();
                    if (is.includes("[object HTML")) return n;
                    (is.includes("WebGL") || is.includes("OscillatorNode") || is.includes("DynamicsCompressorNode") || is.includes("[object Object]")) && (i = !!i), r[tName] = (r[tName] || 0) + 1; // PATCH: g[t], _[i], o[i] removed (write-only; _ and o kept every return value alive)
                    var p = w(tName, e, i, r[tName], a);
                    return p && (fpmonPutRow(p, !tSpecial.length), fpmonTrackRow(p)), n
                };
            // PATCH: when this creates a new own property (document, localStorage, ...), make it non-enumerable,
            // otherwise Object.keys(localStorage) returns ["setItem", "getItem", "removeItem"] on every site.
            // (Assign first: on Storage objects, defineProperty of a missing key would store an item instead.)
            var had = Object.prototype.hasOwnProperty.call(a, e.propName);
            a[e.propName] = wrapper, had || !Object.prototype.hasOwnProperty.call(a, e.propName) || Object.defineProperty(a, e.propName, {
                enumerable: !1
            })
        }
 
        function i(r, o) {
            var n = fpmonOriginal(r, o), // PATCH: live value (innerWidth etc. used to be frozen at injection time)
                i = n;
            if (1 != a) return n;
            if ("getComputedStyle" === o) return n;
            if ("plugins" === o) {
                for (var c = [], g = 0, _ = i.length; g < _; g++) i[g] && c.push(i[g]);
                i = y(c, function(e) {
                    var t = y(e, function(e) {
                        return [e.type, e.suffixes]
                    });
                    return [e.name, e.description, t]
                })
            }
            if ("mimeTypes" === o) {
                for (c = [], g = 0, _ = i.length; g < _; g++) i[g] && c.push(i[g]);
                i = y(c, function(e) {
                    var t = y(e, function(e) {
                        return [e.type, e.suffixes, e.description]
                    });
                    return [e.type, e.description, t]
                })
            }
            if ("permissions" === o) {
                for (c = [], g = 0, _ = i.length; g < _; g++) i[g] && c.push(i[g]);
                i = y(c, function(e) {
                    var t = y(e, function(e) {
                        return [e.type, e.suffixes]
                    });
                    return [e.name, e.description, t]
                })
            }
            -1 !== fpmonBoolProps.indexOf(o) && (i = !!n); // PATCH: was a per-read array literal + for-in (and a leaked global "items")
            var k = r + "." + o; // PATCH: was re-concatenated ~10 times per read, plus once per row of m
            "Intl" === o && (i = fpmonTimeZone(i)), "mediaDevices" === o && fpmonEnumerateDevices(n), s[k] = (s[k] || 0) + 1, e[k] = (e[k] || 0) + 1, p[k] = (p[k] || 0) + 1, t[k] = (t[k] || 0) + 1;
            var d = w(k, "", i, p[k], window);
            return d && ("mediaDevices" === o && void 0 !== fpmonDevicesJSON && (d[2] = fpmonDevicesJSON), fpmonPutRow(d, !0), fpmonTrackRow(d)), n
        }
        attributesToMonitor = {
            navigator: ["userAgent", "platform", "plugins", "doNotTrack", "languages", "product", "productSub", "language", "vendor", "vendorSub", "buildID", "oscpu", "hardwareConcurrency", "cpuClass", "webdriver", "maxTouchPoints", "appVersion", "appCodeName", "cookieEnabled", "enabled", "msDoNotTrack", "appName", "mediaDevices", "userLanguage", "browserLanguage", "systemLanguage", "msMaxTouchPoints", "webkitTemporaryStorage", "webkitPersistentStorage", "onLine", "permissions", "canvas", "dragDrop", "geolocation", "localStorage", "orientation", "touch", "openDatabase", "getBattery", "deviceMemory", "connection"],
            screen: ["width", "height", "availWidth", "availHeight", "availTop", "availLeft", "colorDepth", "pixelDepth", "deviceXDPI", "logicalXDPI", "fontSmoothingEnabled", "screenInfo"],
            window: ["webdriver", "emit", "outerHeight", "outerWidth", "innerWidth", "innerHeight", "devicePixelRatio", "localStorage", "indexedDB", "sessionStorage", "Intl", "openDatabase", "swfobject", "ondeviceproximity", "onuserproximity", "DeviceOrientationEvent", "DeviceMotionEvent"]
        }, window.navigator.monitorFingerprinting = {}, originalValues = {};
        var s = {},
            p = {},
            g = {},
            _ = {};
        for (let e of Object.keys(attributesToMonitor))
            for (let t of attributesToMonitor[e]) {
                // PATCH: remember the native getter per object (live values, no navigator/window name clash),
                // and keep assignments working (window.swfobject = ..., [Replaceable] attributes)
                let obj = "window" !== e ? window[e] : window,
                    getter = obj.__lookupGetter__(t),
                    setter = obj.__lookupSetter__(t),
                    rec = fpmonOrig[e + "." + t] = {
                        obj: obj,
                        get: getter,
                        value: void 0
                    };
                try {
                    rec.value = obj[t], originalValues[t] = rec.value
                } catch (e) {
                    console.log(e)
                }
                obj.__defineGetter__(t, () => i(e, t)), getter ? setter && obj.__defineSetter__(t, function(e) {
                    setter.call(obj, e)
                }) : obj.__defineSetter__(t, function(e) {
                    rec.value = e
                })
            }
        audioContextMethods = ["createAnalyser", "createOscillator", "createGain", "createScriptProcessor", "createDynamicsCompressor"], audioContextMethods.forEach(e => {
            n({
                propName: e,
                obj: window.AudioContext.prototype
            }), c += 1
        }), offlineAudioContextMethods = ["createAnalyser", "createOscillator", "createGain", "createScriptProcessor", "createDynamicsCompressor"], offlineAudioContextMethods.forEach(e => {
            n({
                propName: e,
                obj: window.OfflineAudioContext.prototype
            })
        }), analyserMethods = ["getFloatFrequencyData", "getByteFrequencyData", "getFloatTimeDomainData", "getByteTimeDomainData"], analyserMethods.forEach(e => {
            n({
                propName: e,
                obj: window.AnalyserNode.prototype
            }), c += 1
        }), webGLMethods = ["getParameter", "getSupportedExtensions", "getContextAttributes", "getShaderPrecisionFormat", "getExtension", "readPixels", "getUniformLocation", "getAttribLocation", "clearColor", "enable", "depthFunc", "clear", "createBuffer", "bindBuffer", "bufferData", "createProgram", "createShader", "shaderSource", "compileShader", "attachShader", "linkProgram", "useProgram", "drawArrays"], webGLMethods.forEach(e => {
            n({
                propName: e,
                obj: window.WebGLRenderingContext.prototype
            }), c += 1
        }), webGL2Methods = ["getParameter", "getSupportedExtensions", "getContextAttributes", "getShaderPrecisionFormat", "getExtension", "readPixels", "getUniformLocation", "getAttribLocation", "clearColor", "enable", "depthFunc", "clear", "createBuffer", "bindBuffer", "bufferData", "createProgram", "createShader", "shaderSource", "compileShader", "attachShader", "linkProgram", "useProgram", "drawArrays"], webGL2Methods.forEach(e => {
            n({
                propName: e,
                obj: window.WebGL2RenderingContext.prototype
            })
        }), canvasEltMethods = ["toDataURL", "toBlob"], canvasEltMethods.forEach(e => {
            n({
                propName: e,
                obj: HTMLCanvasElement.prototype
            }), c += 1
        }), canvasMethods = ["getImageData", "getLineDash", "measureText", "isPointInPath", "fillText", "fillRect", "beginPath", "arc", "closePath", "fill"], canvasMethods.forEach(e => {
            n({
                propName: e,
                obj: CanvasRenderingContext2D.prototype
            }), c += 1
        }), otherFunctionsToOverride = [{
            propName: "resolvedOptions().timeZone",
            obj: window.Intl.DateTimeFormat.prototype
        }, {
            propName: "getTimezoneOffset",
            obj: Date.prototype
        }, {
            propName: "getComputedTextLength",
            obj: SVGTextContentElement.prototype
        }, {
            propName: "createElement",
            obj: document
        }, {
            propName: "createElementNS",
            obj: document
        }, {
            propName: "pushState",
            obj: window.history
        }, {
            propName: "getElementsByClassName",
            obj: document
        }, {
            propName: "getElementsByName",
            obj: document
        }, {
            propName: "getElementsByTagName",
            obj: document
        }, {
            propName: "insertBefore",
            obj: document
        }, {
            propName: "appendChild",
            obj: document
        }, {
            propName: "elementFromPoint",
            obj: document
        }, {
            propName: "getVoices",
            obj: speechSynthesis
        }, {
            propName: "setItem",
            obj: localStorage
        }, {
            propName: "getItem",
            obj: localStorage
        }, {
            propName: "removeItem",
            obj: localStorage
        }, {
            propName: "setItem",
            obj: sessionStorage
        }, {
            propName: "getItem",
            obj: sessionStorage
        }, {
            propName: "removeItem",
            obj: sessionStorage
        }, {
            propName: "canPlayType",
            obj: HTMLVideoElement.prototype
        }, {
            propName: "canPlayType",
            obj: HTMLAudioElement.prototype
        }];
        try {
            otherFunctionsToOverride.forEach(n), c += 2
        } catch (e) {
            console.log("[FPMON] Error: " + e)
        }
    }, detectFingerprinting();
    var N = (new Date).getTime();
    // PATCH: page-world readers of glob_extension_score still get the full JSON, built when read
    try {
        Object.defineProperty(window, "glob_extension_score", {
            configurable: !0,
            get: function() {
                return fpmonScoreJSON(!0)
            }
        })
    } catch (e) {}
    // PATCH: the content script asks for the full JSON only when the popup needs it
    window.addEventListener("message", function(e) {
        e.source === window && e.data && "fpmon_request_full_score" === e.data.type && (S((new Date).getTime() - N, !1), D(fpmonScoreJSON(!0), "glob_extension_score_full"))
    }, !1);
    console.log("[FPMON] fingerprinting monitor initiated."), a = 1;
    S((new Date).getTime() - N, !1), fpmonPublish(), numberofcalls = 0, olddata = 0, setTimeout(function() {
        ! function e() {
            numberofcalls += 1, S((new Date).getTime() - N, !1), fpmonPublish(), setTimeout(function() {
                e()
            }, 100 * numberofcalls)
        }()
    }, 10)
}
var actualCode = "(" + inject + ")()";
s.text = "" + actualCode, s.setAttribute("data-myAttri", "key"), (document.head || document.documentElement).appendChild(s), s.remove(); // PATCH: the script has run; don't leave its source in the page's DOM
var share_extension_score = {},
    share_script_origins_internal = {},
    glob_trace_id = null,
    glob_orig_domain = null,
    fpmon_dirty = !1,
    fpmon_full_waiters = [];
window.addEventListener("message", function(e) {
    e.source == window && e.data && e.data.type && ("glob_extension_score" == e.data.type && (share_extension_score = e.data.text, fpmon_dirty = !0), "script_origins_internal" == e.data.type && (share_script_origins_internal = e.data.text), "glob_extension_score_full" == e.data.type && fpmon_full_waiters.splice(0).forEach(function(t) {
        t(e.data.text)
    }))
}, !1), chrome.runtime.onMessage.addListener((e, t, r) => {
    if ("popup" === e.from && "DOMInfo" === e.subject) {
        // PATCH: the full score (with every call record) is only serialized when the popup asks for it
        var o = !1,
            a = function(e) {
                o || (o = !0, r({
                    extension_score: e
                }))
            };
        return fpmon_full_waiters.push(a), window.postMessage({
            type: "fpmon_request_full_score"
        }, "*"), setTimeout(function() {
            a(share_extension_score)
        }, 2e3), !0
    }
    "popup" === e.from && "ScriptInfo" === e.subject && r({
        script_origins_internal: share_script_origins_internal
    })
}), interval3 = setInterval(function() {
    // PATCH: only ping when a new (small) summary arrived, instead of the full log every second forever
    if (fpmon_dirty) {
        fpmon_dirty = !1;
        try {
            chrome.runtime.sendMessage({
                from: "content",
                subject: "showPageAction",
                score: share_extension_score
            })
        } catch (e) {
            clearInterval(interval3)
        }
    }
}, 1e3);
