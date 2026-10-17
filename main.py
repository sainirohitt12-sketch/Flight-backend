import asyncio
import hashlib
import hmac
import json
import logging
import math
import os
import random
import re
import sqlite3
import urllib.parse
import uuid
from datetime import date, datetime, timedelta, timezone
from typing import Any, Literal, Optional

import httpx
import razorpay
from dotenv import load_dotenv
from fastapi import FastAPI, HTTPException, Query, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel, ConfigDict, Field, field_validator, model_validator
import requests
from starlette.concurrency import run_in_threadpool

load_dotenv()
logging.basicConfig(level=os.getenv("LOG_LEVEL", "INFO"))
logger = logging.getLogger("travel_api")

app = FastAPI(title="Travel Search API", version="1.0.0")

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=False,
    allow_methods=["GET", "POST", "OPTIONS"],
    allow_headers=["Content-Type"],
)

AIRPORT_DATA = {
    "DEL": {"name": "Indira Gandhi International (DEL)", "city": "Delhi", "country": "India", "lat": 28.5562, "lon": 77.1000, "terminal": "Terminal 3"},
    "BOM": {"name": "Chhatrapati Shivaji Maharaj (BOM)", "city": "Mumbai", "country": "India", "lat": 19.0896, "lon": 72.8656, "terminal": "Terminal 2"},
    "BLR": {"name": "Kempegowda International (BLR)", "city": "Bangalore", "country": "India", "lat": 13.1986, "lon": 77.7066, "terminal": "Terminal 2"},
    "DIB": {"name": "Dibrugarh Airport (DIB)", "city": "Dibrugarh", "country": "India", "lat": 27.4833, "lon": 95.0167, "terminal": "Terminal 1"},
    "GOI": {"name": "Goa Dabolim Airport (GOI)", "city": "Goa", "country": "India", "lat": 15.3808, "lon": 73.8314, "terminal": "Terminal 1"},
    "JFK": {"name": "John F. Kennedy International (JFK)", "city": "New York", "country": "USA", "lat": 40.6413, "lon": -73.7781, "terminal": "Terminal 4"},
    "MIA": {"name": "Miami International (MIA)", "city": "Miami", "country": "USA", "lat": 25.7959, "lon": -80.2870, "terminal": "Terminal D"},
    "DXB": {"name": "Dubai International (DXB)", "city": "Dubai", "country": "UAE", "lat": 25.2532, "lon": 55.3657, "terminal": "Terminal 3"},
    "DOH": {"name": "Hamad International (DOH)", "city": "Doha", "country": "Qatar", "lat": 25.2731, "lon": 51.6081, "terminal": "Terminal 1"},
    "LHR": {"name": "London Heathrow (LHR)", "city": "London", "country": "UK", "lat": 51.4700, "lon": -0.4543, "terminal": "Terminal 5"},
}

CITY_TO_IATA = {
    "DELHI": "DEL", "NEW DELHI": "DEL", "DEL": "DEL",
    "MUMBAI": "BOM", "BOM": "BOM",
    "BANGALORE": "BLR", "BLR": "BLR",
    "DIBRUGARH": "DIB", "DIB": "DIB",
    "GOA": "GOI", "GOI": "GOI",
    "NEW YORK": "JFK", "JFK": "JFK",
    "MIAMI": "MIA", "MIA": "MIA",
    "DUBAI": "DXB", "DXB": "DXB",
    "DOHA": "DOH", "DOH": "DOH",
    "LONDON": "LHR", "LHR": "LHR",
}

def resolve_airport_code(query: str, fallback: str) -> str:
    cleaned = (query or "").strip().upper()
    for city, code in CITY_TO_IATA.items():
        if city in cleaned:
            return code
    codes = re.findall(r"\b[A-Z]{3}\b", cleaned)
    return codes[-1] if codes else fallback


def getFallbackFlights(origin, destination, departDate, passengers, cabinClass):
    o = (origin or "DEL").upper()
    d = destination or "JFK"
    pass_val = int(passengers) if passengers else 1
    cabin = cabinClass or 'Economy'
    depDate = departDate or '2026-10-20'

    routeSeed = (ord(o[0]) + (ord(o[1]) if len(o) > 1 else 65) + ord(d[0])) % 35
    routePriceOffset = (routeSeed - 15) * 8.5

    cabinMultiplier = 1.0
    if 'business' in cabin.lower():
        cabinMultiplier = 2.7
    elif 'first' in cabin.lower():
        cabinMultiplier = 4.2

    is_indian_route = o in ["DEL", "BOM", "BLR", "DIB", "GOI"] or d in ["DEL", "BOM", "BLR", "DIB", "GOI"]
    
    airlines = [
        {"name": "IndiGo", "code": "6E", "logo": "https://images.kiwi.com/airlines/64/6E.png", "aircraft": "Airbus A320neo", "hub": "DEL", "tier": 0.85},
        {"name": "Air India", "code": "AI", "logo": "https://images.kiwi.com/airlines/64/AI.png", "aircraft": "Airbus A321neo", "hub": "DEL", "tier": 0.95},
        {"name": "Vistara", "code": "UK", "logo": "https://images.kiwi.com/airlines/64/UK.png", "aircraft": "Boeing 787-9", "hub": "DEL", "tier": 0.98}
    ] if is_indian_route else [
        {"name": "Emirates", "code": "EK", "logo": "https://images.kiwi.com/airlines/64/EK.png", "aircraft": "Airbus A380-800", "hub": "DXB", "tier": 1.15},
        {"name": "Qatar Airways", "code": "QR", "logo": "https://images.kiwi.com/airlines/64/QR.png", "aircraft": "Airbus A350-1000", "hub": "DOH", "tier": 1.12},
        {"name": "Turkish Airlines", "code": "TK", "logo": "https://images.kiwi.com/airlines/64/TK.png", "aircraft": "Boeing 787-9 Dreamliner", "hub": "IST", "tier": 0.98}
    ]

    schedules = [
        {"dep": "06:30", "depMin": 390, "nonstop": True},
        {"dep": "10:10", "depMin": 610, "nonstop": True},
        {"dep": "14:25", "depMin": 865, "nonstop": False, "layover": "1h 45m"},
        {"dep": "19:45", "depMin": 1185, "nonstop": True}
    ]

    results = []
    for i, sch in enumerate(schedules):
        air = airlines[i % len(airlines)]
        isDirect = sch["nonstop"]
        durHours = 2.5 if is_indian_route else 14.5
        durMins = int(durHours * 60)
        h = durMins // 60
        m = durMins % 60
        durFormatted = f"{h}h {m:02d}m"

        arrTotalMins = sch["depMin"] + durMins
        arrH = (arrTotalMins % 1440) // 60
        arrM = arrTotalMins % 60
        arrFormatted = f"{arrH:02d}:{arrM:02d}"

        basePrice = (120 if is_indian_route else (720 + routePriceOffset)) * air["tier"] * cabinMultiplier
        totalPrice = round(basePrice * pass_val, 2)
        flightNum = f"{air['code']}-{100 + ((i * 37) % 890)}"

        results.append({
            "id": f"FL-{o}-{d}-{air['code']}-{i+1}",
            "airline": air["name"],
            "airline_logo": air["logo"],
            "flight_number": flightNum,
            "aircraft": air["aircraft"],
            "origin": o,
            "destination": d,
            "origin_airport": "Terminal 1",
            "dest_airport": "Terminal 3",
            "depart_date": str(depDate),
            "departure_time": sch["dep"],
            "arrival_time": arrFormatted,
            "duration_formatted": durFormatted,
            "duration_minutes": durMins,
            "stops_count": 0 if isDirect else 1,
            "layover_airport": None if isDirect else air["hub"],
            "layover_duration": None if isDirect else sch.get("layover"),
            "price_usd": totalPrice,
            "price_ava": round(totalPrice / 0.55, 1),
            "cabin_class": cabin,
            "passengers": pass_val
        })
    return results


@app.get("/api/flights/search")
async def flights_search_full(
    origin: Optional[str] = Query(default=None),
    destination: Optional[str] = Query(default=None),
    depart_date: Optional[date] = Query(default=None),
    return_date: Optional[date] = Query(default=None),
    passengers: int = Query(default=1, ge=1, le=9),
    cabin_class: str = Query(default="Economy"),
):
    o_code = resolve_airport_code(origin, "DEL") if origin else "DEL"
    d_code = resolve_airport_code(destination, "JFK") if destination else "JFK"

    orig_name = AIRPORT_DATA.get(o_code, {}).get("name", f"{o_code} Airport")
    dest_name = AIRPORT_DATA.get(d_code, {}).get("name", f"{d_code} Airport")

    if not depart_date:
        depart_date = date.today() + timedelta(days=5)
    if not return_date:
        return_date = depart_date + timedelta(days=1)

    results = []
    generated = getFallbackFlights(o_code, d_code, depart_date, passengers, cabin_class)
    for f in generated:
        orig_usd = f["price_usd"]
        disc_usd = round(orig_usd * 0.80, 2)
        f["price_usd"] = disc_usd
        f["total_price"] = disc_usd
        f["price"] = round(disc_usd / passengers, 2)
        f["price_formatted"] = f"US$ {disc_usd:,.2f}"
        f["giveback_formatted"] = f"US$ {round(disc_usd * 0.03, 2):.2f}"
        f["price_ava"] = round(disc_usd / 0.55, 1)
        results.append(f)

    return {
        "status": "ok",
        "origin": orig_name,
        "origin_code": o_code,
        "destination": dest_name,
        "destination_code": d_code,
        "depart_date": depart_date.isoformat(),
        "return_date": return_date.isoformat(),
        "passengers": passengers,
        "cabin_class": cabin_class,
        "total_flights": len(results),
        "flights": results,
    }


@app.get("/")
@app.get("/index.html")
def serve_index():
    return FileResponse(os.path.join(os.path.dirname(__file__), "index.html"))

@app.get("/search.html")
def serve_search():
    return FileResponse(os.path.join(os.path.dirname(__file__), "search.html"))
