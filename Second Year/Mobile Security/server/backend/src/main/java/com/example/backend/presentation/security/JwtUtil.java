package com.example.backend.presentation.security;

import io.jsonwebtoken.Claims;
import io.jsonwebtoken.Jwts;
import io.jsonwebtoken.security.Keys;

import org.springframework.beans.factory.annotation.Value;
import org.springframework.stereotype.Component;

import java.util.Date;

import javax.crypto.SecretKey;

@Component
public class JwtUtil {

    @Value("${jwt.secret}")
    private String jwtSecret;

    public String getUsernameFromToken(String token) {
        var secretKey = getSecretKey(this.jwtSecret);
        Claims claims = Jwts.parser().verifyWith(secretKey).build().parseSignedClaims(token).getPayload();
        return claims.getSubject();
    }

    public Date getExpirationDateFromToken(String token) {
        var secretKey = getSecretKey(this.jwtSecret);
        Claims claims = Jwts.parser().verifyWith(secretKey).build().parseSignedClaims(token).getPayload();
        return claims.getExpiration();
    }

    public Long getIdFromToken(String token) {
        var secretKey = getSecretKey(this.jwtSecret);
        Claims claims = Jwts.parser().verifyWith(secretKey).build().parseSignedClaims(token).getPayload();
        return claims.get("id", Long.class);
    }

    public Boolean validateToken(String token) {
        try {
            SecretKey key = getSecretKey(this.jwtSecret);
            Jwts.parser().decryptWith(key).build().parseSignedClaims(token);
            return true;
        } catch (Exception e) {
            return false;
        }
    }

    private SecretKey getSecretKey(String secret) {
        byte[] keyBytes = secret.getBytes();
        return Keys.hmacShaKeyFor(keyBytes);
    }
}
